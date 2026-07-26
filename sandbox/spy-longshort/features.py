"""Expert signals for the SPY long/short book.

Every column returned by :func:`build_panel` is *strictly causal*: the value at
row ``t`` uses only information observable at the close of day ``t``.  The
target ``r_fwd`` is the excess return earned between close ``t`` and close
``t+1`` -- i.e. the payoff of a position taken on the signal at ``t``.

The signals are deliberately boring and well known.  The point of this project
is not signal novelty; it is what the PIT / game / statistics layers do with a
pool of mediocre, correlated, partly-dead predictors.
"""

from __future__ import annotations

import os

import numpy as np
import pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

# Sign convention: every expert is written so that "higher = more bullish".
EXPERTS = [
    "trend_200",   # price above its 200d average
    "mom_12_1",    # 12-month momentum skipping the last month
    "mom_63",      # 3-month momentum
    "rev_5",       # 1-week short-term reversal
    "rev_1",       # 1-day reversal
    "lowvol",      # low realised volatility
    "vrp",         # variance risk premium (VIX - realised vol)
    "vix_spike",   # VIX stretched above its own 20d average
    "tom",         # turn-of-month seasonality
    "drawdown",    # distance below the trailing 1y high
]


def _load(name: str) -> pd.DataFrame:
    frame = pd.read_csv(os.path.join(DATA, f"{name}.csv"), parse_dates=["date"])
    return frame.set_index("date")


def build_panel() -> pd.DataFrame:
    spy, vix, irx = _load("SPY"), _load("VIX"), _load("IRX")

    px = spy["adjclose"].astype(float)
    ret = np.log(px).diff()

    # Risk-free: ^IRX is an annualised discount rate in percent.
    rf = (irx["close"].astype(float) / 100.0 / 252.0).reindex(px.index).ffill()
    rf = rf.fillna(0.0)
    excess = ret - rf

    vixc = vix["close"].astype(float).reindex(px.index).ffill()
    rvol = ret.rolling(21).std() * np.sqrt(252) * 100.0  # in VIX units

    panel = pd.DataFrame(index=px.index)
    panel["px"] = px
    panel["ret"] = ret
    panel["rf"] = rf
    panel["excess"] = excess

    panel["trend_200"] = np.log(px / px.rolling(200).mean())
    panel["mom_12_1"] = np.log(px.shift(21) / px.shift(252))
    panel["mom_63"] = np.log(px / px.shift(63))
    panel["rev_5"] = -np.log(px / px.shift(5))
    panel["rev_1"] = -ret
    panel["lowvol"] = -ret.rolling(21).std()
    panel["vrp"] = vixc - rvol
    panel["vix_spike"] = np.log(vixc / vixc.rolling(20).mean())
    panel["tom"] = _turn_of_month(px.index)
    panel["drawdown"] = np.log(px / px.rolling(252).max())

    # Payoff of a position opened at the close of t.
    panel["r_fwd"] = excess.shift(-1)

    return panel


def _turn_of_month(index: pd.DatetimeIndex) -> pd.Series:
    """1 on the last trading day of a month and the first three of the next.

    Uses the exchange calendar only, which is public in advance -- the
    ``shift(-1)`` reads tomorrow's *date*, never tomorrow's price.
    """
    month = pd.Series(index.year * 12 + index.month, index=index)
    is_last = month != month.shift(-1)
    rank_in_month = month.groupby(month).cumcount()
    return (is_last | (rank_in_month < 3)).astype(float)
