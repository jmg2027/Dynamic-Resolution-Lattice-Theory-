"""A survivorship-light ETF universe with causal entry.

Why ETFs and not S&P 500 members.  The obvious way to buy breadth is a stock
cross-section, but a *current* constituent list is poisoned: today's members are
the ones that did not go bankrupt, get delisted, or get taken under.  Building
an unbiased point-in-time constituent history is a data problem, not a research
problem, and getting it wrong produces exactly the kind of result this project
exists to detect.

ETFs are the cheap way out.  Two properties matter:

* **Closure is not a -100% return.**  When an ETF shuts it liquidates at NAV,
  so the return path of a dead fund is not catastrophically different from a
  live one.  The survivorship bias that remains is a bias in *which exposures*
  are represented, not in their returns -- far weaker than the stock case.
* **The big country and sector funds essentially do not close.**  The iShares
  MSCI single-country line and the sector SPDRs below have traded continuously
  since 1996 and 1998.

Entry is causal: a fund becomes eligible only once it has ``min_history``
trading days behind it, so the universe grows from ~20 names in 1997 to ~50
today exactly as it did in reality.  Nothing is back-filled.
"""

from __future__ import annotations

import json
import os
import time
import urllib.parse
import urllib.request

import numpy as np
import pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
URL = ("https://query1.finance.yahoo.com/v8/finance/chart/{sym}"
       "?period1=0&period2=9999999999&interval=1d&events=div%7Csplit")

# Grouped only for reporting -- the strategy sees one undifferentiated pool.
GROUPS = {
    "country": ["EWA", "EWC", "EWD", "EWG", "EWH", "EWI", "EWJ", "EWK", "EWL",
                "EWM", "EWN", "EWO", "EWP", "EWQ", "EWS", "EWU", "EWW",
                "EWT", "EWY", "EWZ", "EZA"],
    "region": ["EFA", "EEM", "EPP", "IEV", "ILF"],
    "us_sector": ["XLB", "XLE", "XLF", "XLI", "XLK", "XLP", "XLU", "XLV", "XLY"],
    "us_style": ["SPY", "MDY", "QQQ", "DIA", "IWM", "IWD", "IWF", "IJH", "IJR"],
    "rates_credit": ["TLT", "IEF", "SHY", "LQD", "TIP", "HYG", "AGG"],
    "real_assets": ["GLD", "SLV", "IYR", "DBC", "USO"],
}
TICKERS = [t for g in GROUPS.values() for t in g]
GROUP_OF = {t: g for g, ts in GROUPS.items() for t in ts}
BENCHMARK = "SPY"
RISK_FREE = "IRX"  # ^IRX, fetched separately


def fetch_one(symbol: str, yahoo: str | None = None) -> pd.DataFrame | None:
    req = urllib.request.Request(
        URL.format(sym=urllib.parse.quote(yahoo or symbol)),
        headers={"User-Agent": "Mozilla/5.0"},
    )
    try:
        with urllib.request.urlopen(req, timeout=60) as fh:
            payload = json.load(fh)
        result = payload["chart"]["result"][0]
    except Exception as exc:  # noqa: BLE001 -- a dead ticker must not stop the run
        print(f"  {symbol:5s} FAILED  {exc}")
        return None
    quote = result["indicators"]["quote"][0]
    adj = result["indicators"].get("adjclose")
    close = adj[0]["adjclose"] if adj else quote["close"]
    frame = pd.DataFrame({
        "date": pd.to_datetime(result["timestamp"], unit="s").normalize(),
        "adjclose": close,
        "volume": quote["volume"],
    })
    return frame.dropna(subset=["adjclose"]).drop_duplicates("date") \
                .sort_values("date").reset_index(drop=True)


def fetch_all(pause: float = 0.3) -> None:
    os.makedirs(DATA, exist_ok=True)
    for symbol, yahoo in [(t, None) for t in TICKERS] + [(RISK_FREE, "^IRX")]:
        frame = fetch_one(symbol, yahoo)
        if frame is None or len(frame) < 260:
            print(f"  {symbol:5s} skipped ({0 if frame is None else len(frame)} rows)")
            continue
        frame.to_csv(os.path.join(DATA, f"{symbol}.csv"), index=False)
        print(f"  {symbol:5s} {len(frame):6d}  {frame['date'].iloc[0].date()}"
              f" -> {frame['date'].iloc[-1].date()}")
        time.sleep(pause)


def load_prices(min_history: int = 252) -> tuple[pd.DataFrame, pd.Series, pd.DataFrame]:
    """Return ``(prices, risk_free, eligible)`` on a common trading calendar.

    ``eligible[t, i]`` is True once asset ``i`` has ``min_history`` observations
    at or before ``t`` -- the causal entry rule.  Assets never leave.
    """
    frames = {}
    for ticker in TICKERS:
        path = os.path.join(DATA, f"{ticker}.csv")
        if os.path.exists(path):
            f = pd.read_csv(path, parse_dates=["date"]).set_index("date")
            frames[ticker] = f["adjclose"].astype(float)
    prices = pd.DataFrame(frames).sort_index()

    # Trade only on days the benchmark trades, so the calendar is a real one.
    spy = pd.read_csv(os.path.join(DATA, f"{BENCHMARK}.csv"),
                      parse_dates=["date"]).set_index("date")
    prices = prices.reindex(spy.index)

    irx = pd.read_csv(os.path.join(DATA, f"{RISK_FREE}.csv"),
                      parse_dates=["date"]).set_index("date")["adjclose"]
    rf = (irx.astype(float) / 100.0 / 252.0).reindex(prices.index).ffill().fillna(0.0)

    observed = prices.notna()
    eligible = observed.cumsum() >= min_history
    # Forward-fill at most 5 days of missing quotes; longer gaps stay ineligible.
    prices = prices.ffill(limit=5)
    eligible &= prices.notna()
    return prices, rf, eligible


def summary(prices: pd.DataFrame, eligible: pd.DataFrame) -> dict:
    counts = eligible.sum(axis=1)
    starts = {t: str(prices[t].first_valid_index().date()) for t in prices.columns}
    return {
        "n_tickers": int(prices.shape[1]),
        "first_date": str(prices.index[0].date()),
        "last_date": str(prices.index[-1].date()),
        "breadth_first_eligible_date": str(counts[counts >= 10].index[0].date()),
        "breadth_min": int(counts[counts > 0].min()),
        "breadth_median": float(counts.median()),
        "breadth_max": int(counts.max()),
        "listing_dates": starts,
        "groups": {g: [t for t in ts if t in prices.columns]
                   for g, ts in GROUPS.items()},
    }


if __name__ == "__main__":
    fetch_all()
    px, rf, elig = load_prices()
    info = summary(px, elig)
    print(f"\n{info['n_tickers']} tickers  {info['first_date']} -> {info['last_date']}"
          f"   breadth {info['breadth_min']} -> {info['breadth_max']}"
          f" (median {info['breadth_median']:.0f})")
