"""Download daily history for SPY, ^VIX, ^IRX from the Yahoo chart endpoint.

Writes one CSV per symbol into ``data/``.  Adjusted close is reconstructed from
the ``adjclose`` block when present, otherwise from raw close.

Usage:  python3 fetch_data.py
"""

from __future__ import annotations

import json
import os
import urllib.request

import pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
URL = (
    "https://query1.finance.yahoo.com/v8/finance/chart/{sym}"
    "?period1=0&period2=9999999999&interval=1d&events=div%7Csplit"
)
SYMBOLS = {"SPY": "SPY", "VIX": "^VIX", "IRX": "^IRX"}


def fetch(symbol: str) -> pd.DataFrame:
    req = urllib.request.Request(
        URL.format(sym=urllib.parse.quote(symbol)),
        headers={"User-Agent": "Mozilla/5.0"},
    )
    with urllib.request.urlopen(req, timeout=60) as fh:
        payload = json.load(fh)
    return parse(payload)


def parse(payload: dict) -> pd.DataFrame:
    result = payload["chart"]["result"][0]
    quote = result["indicators"]["quote"][0]
    frame = pd.DataFrame(
        {
            "date": pd.to_datetime(result["timestamp"], unit="s").normalize(),
            "open": quote["open"],
            "high": quote["high"],
            "low": quote["low"],
            "close": quote["close"],
            "volume": quote["volume"],
        }
    )
    adj = result["indicators"].get("adjclose")
    frame["adjclose"] = adj[0]["adjclose"] if adj else frame["close"]
    frame = frame.dropna(subset=["adjclose"]).drop_duplicates("date")
    return frame.sort_values("date").reset_index(drop=True)


def main() -> None:
    os.makedirs(DATA, exist_ok=True)
    for name, symbol in SYMBOLS.items():
        frame = fetch(symbol)
        path = os.path.join(DATA, f"{name}.csv")
        frame.to_csv(path, index=False)
        print(f"{name:5s} {len(frame):6d} rows  "
              f"{frame['date'].iloc[0].date()} -> {frame['date'].iloc[-1].date()}")


if __name__ == "__main__":
    main()
