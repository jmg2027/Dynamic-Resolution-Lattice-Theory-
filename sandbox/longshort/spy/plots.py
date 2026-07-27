"""Charts for the SPY long/short book.  Run after ``backtest.py``.

Usage:  python3 plots.py
"""

from __future__ import annotations

import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

from spy import features

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")

INK = "#1c1c1c"
ACCENT = "#c2410c"
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


def main() -> None:
    daily = pd.read_csv(os.path.join(OUT, "daily.csv"), index_col=0,
                        parse_dates=True)
    with open(os.path.join(OUT, "results.json")) as fh:
        res = json.load(fh)
    placebo = np.load(os.path.join(OUT, "placebo_sharpes.npy"))

    fig, axes = plt.subplots(3, 2, figsize=(13, 11))
    fig.patch.set_facecolor("white")

    # 1 -- equity curves
    ax = axes[0, 0]
    for col, label, color, lw in [
        ("buy_hold", "SPY buy & hold", MUTED, 1.4),
        ("net", "strategy, net of 2bp", ACCENT, 1.4),
        ("gross", "strategy, gross", "#fdba74", 1.0),
    ]:
        ax.plot(daily.index, np.cumprod(1 + daily[col].fillna(0)),
                label=label, color=color, lw=lw)
    ax.set_yscale("log")
    ax.legend(fontsize=7, frameon=False)
    _style(ax, "Growth of 1 (log scale)", "multiple")

    # 2 -- placebo distribution
    ax = axes[0, 1]
    ax.hist(placebo, bins=40, color=MUTED, edgecolor="white", lw=0.4)
    obs = res["strategy_net"]["sharpe"]
    ax.axvline(obs, color=ACCENT, lw=1.8)
    ax.axvline(np.percentile(placebo, 95), color=INK, lw=1.0, ls="--")
    ax.annotate(f"observed {obs:+.2f}\np = {res['placebo']['p_value']:.2f}",
                xy=(obs, ax.get_ylim()[1] * 0.75), xytext=(8, 0),
                textcoords="offset points", fontsize=8, color=ACCENT)
    ax.annotate("95th pct of null", xy=(np.percentile(placebo, 95), 0),
                xytext=(6, 6), textcoords="offset points", fontsize=7, color=INK)
    _style(ax, f"Placebo: same pipeline on {len(placebo)} block-permuted "
               "return series", "draws")
    ax.set_xlabel("annualised Sharpe", fontsize=8)

    # 3 -- position and no-trade band, zoomed so the mechanism is legible
    ax = axes[1, 0]
    win = daily.loc["2019-06-01":"2020-12-31"]
    ax.fill_between(win.index, win["pos"] - win["band"], win["pos"] + win["band"],
                    color="#fed7aa", alpha=0.6, lw=0, label="no-trade band")
    ax.plot(win.index, win["target"], color=MUTED, lw=0.9,
            label="frictionless Kelly target")
    ax.plot(win.index, win["pos"], color=ACCENT, lw=1.3, label="held position")
    ax.axhline(0, color=INK, lw=0.6)
    ax.legend(fontsize=7, frameon=False, loc="lower left")
    _style(ax, "Position vs target, 2019-2020 detail: the band absorbs the churn",
           "exposure")

    # 4 -- Hedge weights
    ax = axes[1, 1]
    names = features.EXPERTS
    weights = daily[[f"w_{n}" for n in names]].to_numpy().T
    ax.stackplot(daily.index, weights, labels=names,
                 colors=plt.cm.tab20(np.linspace(0, 1, len(names))), lw=0)
    ax.set_ylim(0, 1)
    ax.legend(fontsize=6, frameon=False, ncol=2, loc="upper left")
    _style(ax, "Hedge weights: capital defunds a dead expert without being told",
           "weight")

    # 5 -- PIT calibration
    ax = axes[2, 0]
    u = daily["pit"].dropna().to_numpy()
    ax.hist(u, bins=20, range=(0, 1), color=MUTED, edgecolor="white", lw=0.4,
            density=True)
    ax.axhline(1.0, color=ACCENT, lw=1.4, label="U(0,1) if correctly specified")
    ax.legend(fontsize=7, frameon=False)
    c = res["calibration"]
    _style(ax, f"PIT of realised returns through the predictive law  "
               f"(KS={c['ks_stat']:.3f}, p={c['ks_pvalue']:.3f})", "density")

    # 6 -- rolling Sharpe
    ax = axes[2, 1]
    win = 504
    for col, label, color in [("net", "strategy", ACCENT),
                              ("buy_hold", "SPY", MUTED)]:
        r = daily[col].fillna(0)
        roll = r.rolling(win).mean() / r.rolling(win).std() * np.sqrt(252)
        ax.plot(daily.index, roll, color=color, lw=1.1, label=label)
    ax.axhline(0, color=INK, lw=0.6)
    ax.legend(fontsize=7, frameon=False)
    _style(ax, "Rolling 2-year Sharpe", "Sharpe")

    fig.tight_layout(pad=1.6)
    path = os.path.join(OUT, "report.png")
    fig.savefig(path, dpi=145, facecolor="white")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
