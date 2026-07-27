"""Cross-sectional experts, and the PIT that gets cleaner when you go wide.

In the SPY book the probability integral transform had to be run through an
*expanding* window: with one asset, the only reference distribution for today's
momentum reading is its own history, so the transform inherits a burn-in and a
slowly-drifting reference set.

In cross-section the transform is taken **across assets at a single instant**.
It is exactly causal by construction -- no window, no burn-in, no drift, and no
possibility of leakage, because nothing from any other date enters.  It also
does more work: it strips out whatever moved every asset that day, so what
survives the rank is the relative view, which is the only thing a market-neutral
book can actually trade.

Each expert then becomes a zero-cost portfolio: score, rank, demean,
risk-weight, normalise to a fixed ex-ante volatility.  The backtest downstream
never sees an asset -- it sees eight portfolio return streams, which puts it in
exactly the shape the SPY pipeline already knew how to audit.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
from scipy.stats import norm

from common import edge as edge_mod

EXPERTS = [
    "mom_12_1",    # 12-month momentum skipping the last month
    "mom_63",      # 3-month momentum
    "mom_21",      # 1-month momentum
    "rev_5",       # 1-week reversal
    "rev_1",       # 1-day reversal
    "trend_200",   # price above its own 200d average
    "lowvol",      # low realised volatility
    "drawdown",    # distance below the trailing 1y high
]
TARGET_VOL = 0.01  # ex-ante daily vol of each unit expert portfolio


def raw_signals(prices: pd.DataFrame) -> dict[str, pd.DataFrame]:
    logp = np.log(prices)
    ret = logp.diff()
    return {
        "mom_12_1": logp.shift(21) - logp.shift(252),
        "mom_63": logp - logp.shift(63),
        "mom_21": logp - logp.shift(21),
        "rev_5": -(logp - logp.shift(5)),
        "rev_1": -ret,
        "trend_200": logp - np.log(prices.rolling(200).mean()),
        "lowvol": -ret.rolling(21).std(),
        "drawdown": logp - np.log(prices.rolling(252).max()),
    }


def cross_sectional_pit(raw: pd.DataFrame, eligible: pd.DataFrame,
                        min_names: int = 8) -> pd.DataFrame:
    """Rank across assets within each date, then map to normal scores.

    Causal with no window: the reference distribution is the other assets
    *today*.  Rows with fewer than ``min_names`` eligible assets are dropped
    rather than ranked, since a rank over five names is mostly noise.
    """
    masked = raw.where(eligible & raw.notna())
    count = masked.notna().sum(axis=1)
    ranks = masked.rank(axis=1, method="average")
    u = ranks.sub(0.5).div(count, axis=0)
    z = pd.DataFrame(norm.ppf(np.clip(u.to_numpy(), 1e-6, 1 - 1e-6)),
                     index=raw.index, columns=raw.columns)
    z = z.where(masked.notna())
    z = z.sub(z.mean(axis=1), axis=0)          # exactly dollar-neutral in score
    return z.where(count.ge(min_names), np.nan)


def expert_weights(z: pd.DataFrame, vol: pd.DataFrame,
                   target_vol: float = TARGET_VOL) -> pd.DataFrame:
    """Risk-weighted, zero-cost, unit-risk portfolio from a score panel.

    ``w_i = z_i / sigma_i`` equalises each name's risk contribution, which is
    what stops a 40%-vol Brazil ETF from being the whole book against a 2%-vol
    T-bill fund.  Normalising by ``||z||_2`` sets ex-ante portfolio volatility
    to ``target_vol`` under an independence assumption; realised correlation
    makes the true figure larger, which the Kelly layer then measures directly
    rather than assuming.
    """
    zz = z.fillna(0.0)
    w = zz / vol.where(vol > 0)
    norm_z = np.sqrt((zz ** 2).sum(axis=1))
    w = w.div(norm_z.where(norm_z > 0), axis=0) * target_vol
    return w.replace([np.inf, -np.inf], np.nan).fillna(0.0)


def build(prices: pd.DataFrame, rf: pd.Series, eligible: pd.DataFrame,
          vol_halflife: float = 21.0) -> dict:
    """Assemble score panels, expert portfolios and their realised IC."""
    ret = np.log(prices).diff()
    excess = ret.sub(rf, axis=0).where(eligible)
    r_fwd = excess.shift(-1)

    vol = pd.DataFrame(
        {c: edge_mod.ewma_vol(ret[c].to_numpy(dtype=float), halflife=vol_halflife)
         for c in prices.columns},
        index=prices.index,
    ).where(eligible)

    raws = raw_signals(prices)
    z = {k: cross_sectional_pit(v, eligible & vol.notna()) for k, v in raws.items()}
    weights = {k: expert_weights(v, vol) for k, v in z.items()}

    q = pd.DataFrame(
        {k: (w * r_fwd.fillna(0.0)).sum(axis=1).where(w.abs().sum(axis=1) > 0)
         for k, w in weights.items()}
    )
    ic = pd.DataFrame({k: _spearman_by_row(v, r_fwd) for k, v in z.items()})

    return {"excess": excess, "r_fwd": r_fwd, "vol": vol, "z": z,
            "weights": weights, "q": q, "ic": ic,
            "breadth": eligible.sum(axis=1)}


def _spearman_by_row(z: pd.DataFrame, r_fwd: pd.DataFrame) -> pd.Series:
    """Daily cross-sectional rank correlation -- the IC in IR = IC * sqrt(N)."""
    a = z.where(r_fwd.notna())
    b = r_fwd.where(z.notna())
    ra = a.rank(axis=1)
    rb = b.rank(axis=1)
    ra = ra.sub(ra.mean(axis=1), axis=0)
    rb = rb.sub(rb.mean(axis=1), axis=0)
    num = (ra * rb).sum(axis=1)
    den = np.sqrt((ra ** 2).sum(axis=1) * (rb ** 2).sum(axis=1))
    out = num / den.where(den > 0)
    return out.where(a.notna().sum(axis=1) >= 8)
