"""Charts for the cross-sectional ETF book.  Run after ``xsec.backtest``.

Usage:  python3 -m xsec.plots
"""

from __future__ import annotations

import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from dataclasses import replace

from xsec import backtest, features

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")

INK = "#1c1c1c"
ACCENT = "#c2410c"
WARN = "#0e7490"
MUTED = "#94a3b8"
GRID = {"color": "#e5e7eb", "lw": 0.6}


def _style(ax, title: str, ylabel: str = "") -> None:
    ax.set_title(title, fontsize=10, color=INK, loc="left", pad=6)
    ax.set_ylabel(ylabel, fontsize=8, color=INK)
    ax.tick_params(labelsize=7, colors=INK, length=2)
    ax.grid(True, **GRID)
    ax.set_axisbelow(True)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(MUTED)


def lag_curves(cfg: backtest.Config) -> dict[int, pd.Series]:
    """Net equity curve at 0, 1 and 2 days between signal and execution."""
    prep = backtest.prepare(cfg)
    dates = prep["r_fwd"].index
    curves = {}
    for lag in (0, 1, 2):
        out = backtest.pipeline(prep, prep["r_fwd"], replace(cfg, impl_lag=lag),
                                full=False)
        sl = slice(out["start"], len(dates) - 1)
        curves[lag] = pd.Series(out["net"][sl], index=dates[sl])
    return curves


def main() -> None:
    daily = pd.read_csv(os.path.join(OUT, "daily.csv"), index_col=0, parse_dates=True)
    with open(os.path.join(OUT, "results.json")) as fh:
        res = json.load(fh)
    cfg = backtest.Config(**{k: v for k, v in res["config"].items()})
    placebo = np.load(os.path.join(OUT, "placebo_sharpes_net.npy"))
    curves = lag_curves(cfg)

    fig, axes = plt.subplots(3, 2, figsize=(13, 11))
    fig.patch.set_facecolor("white")

    # 1 -- the artefact, in one picture
    ax = axes[0, 0]
    for lag, color, lw in [(0, WARN, 1.6), (1, ACCENT, 1.6), (2, MUTED, 1.2)]:
        sr = res["strategy_net"]["sharpe"] if lag == 1 else \
            res[f"implementation_lag_{lag}d"]["sharpe"]
        ax.plot(curves[lag].index, np.cumprod(1 + curves[lag].fillna(0)),
                color=color, lw=lw, label=f"execute at close t+{lag}   SR={sr:+.2f}")
    ax.set_yscale("log")
    ax.legend(fontsize=7.5, frameon=False, loc="upper left")
    _style(ax, "The whole edge is one day old: same-close execution vs +1 day",
           "growth of 1 (log)")

    # 2 -- placebo
    ax = axes[0, 1]
    ax.hist(placebo, bins=40, color=MUTED, edgecolor="white", lw=0.4)
    obs = res["strategy_net"]["sharpe"]
    ax.axvline(obs, color=ACCENT, lw=1.8)
    ax.axvline(np.percentile(placebo, 95), color=INK, lw=1.0, ls="--")
    ax.annotate(f"observed {obs:+.2f}\np = {res['placebo']['p_value']:.3f}",
                xy=(obs, ax.get_ylim()[1] * 0.7), xytext=(8, 0),
                textcoords="offset points", fontsize=8, color=ACCENT)
    _style(ax, f"Placebo: same pipeline on {len(placebo)} date-permuted "
               "return panels", "draws")
    ax.set_xlabel("annualised Sharpe", fontsize=8)

    # 3 -- IC decay: where the artefact lived and when it died
    ax = axes[1, 0]
    for name, color in [("rev_1", WARN), ("rev_5", ACCENT), ("mom_12_1", "#7c3aed")]:
        roll = daily[f"ic_{name}"].rolling(504, min_periods=252).mean()
        ax.plot(daily.index, roll, color=color, lw=1.3, label=name)
    ax.axhline(0, color=INK, lw=0.7)
    ax.legend(fontsize=7.5, frameon=False)
    _style(ax, "Rolling 2-year information coefficient", "mean daily rank corr")

    # 4 -- Hedge weights
    ax = axes[1, 1]
    names = features.EXPERTS
    ax.stackplot(daily.index, daily[[f"w_{n}" for n in names]].to_numpy().T,
                 labels=names, colors=plt.cm.tab20(np.linspace(0, 1, len(names))),
                 lw=0)
    ax.set_ylim(0, 1)
    ax.legend(fontsize=6, frameon=False, ncol=2, loc="upper left")
    _style(ax, "Hedge weights over the expert pool", "weight")

    # 5 -- breadth and gross exposure
    ax = axes[2, 0]
    ax.plot(daily.index, daily["breadth"], color=MUTED, lw=1.2,
            label="eligible ETFs")
    ax.plot(daily.index, daily["n_positions"], color=ACCENT, lw=1.0,
            label="names held")
    ax.legend(fontsize=7.5, frameon=False, loc="upper left")
    _style(ax, "Universe grows as funds list -- nothing is back-filled", "names")
    twin = ax.twinx()
    twin.plot(daily.index, daily["gross_exposure"], color=WARN, lw=0.8, alpha=0.7)
    twin.set_ylabel("gross exposure", fontsize=8, color=WARN)
    twin.tick_params(labelsize=7, colors=WARN, length=2)
    for side in ("top", "left"):
        twin.spines[side].set_visible(False)

    # 6 -- rolling Sharpe
    ax = axes[2, 1]
    win = 504
    for col, label, color in [("net", "strategy (+1d)", ACCENT),
                              ("buy_hold", "SPY", MUTED)]:
        r = daily[col].fillna(0)
        ax.plot(daily.index, r.rolling(win).mean() / r.rolling(win).std()
                * np.sqrt(252), color=color, lw=1.1, label=label)
    ax.axhline(0, color=INK, lw=0.7)
    ax.legend(fontsize=7.5, frameon=False)
    _style(ax, "Rolling 2-year Sharpe", "Sharpe")

    fig.tight_layout(pad=1.6)
    path = os.path.join(OUT, "report.png")
    fig.savefig(path, dpi=145, facecolor="white")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
