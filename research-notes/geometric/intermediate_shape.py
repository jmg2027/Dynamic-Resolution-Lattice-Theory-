"""The shape at an *intermediate* stage of between-pointing (not the limit).

The limit of iterated betweenness is the bare segment [a,b]: structureless, every
interior point alike.  All the content lives at FINITE generation n.  There each
relation-point carries a depth = the generation it was born = how many times the
interval it bridges has been halved = its resolution.  For the dyadic point
k/2^n that depth is  n - v2(k)  (v2 = 2-adic valuation): the *ruler sequence*.

Two readings of "the shape at stage n":

  (1) the resolution hierarchy itself — generation k contributes one tent of
      height 2^-k over every gap it bridges (k=0 is c, the first midpoint, the
      tallest; k=1 is d,e; ...).  These tents are self-similar: the stage-n
      picture contains a half-scale copy of stage-(n-1).

  (2) their sum, the finite Takagi (blancmange) approximation
          T_n(x) = sum_{k=0}^{n} 2^-k * dist(2^k x, nearest integer).
      As n grows this converges to the Takagi function: continuous, nowhere
      differentiable, self-similar.  So the *positions* flatten to a segment,
      but the *shape of how they were reached* is a fractal — and it is exactly
      this resolution-indexed object, the dynamic-resolution lattice, that the
      limit erases.

Run:  python3 research-notes/geometric/intermediate_shape.py
"""

import numpy as np
import matplotlib.pyplot as plt


def tent(y):
    """Distance from y to the nearest integer (the unit tent, peak 1/2)."""
    return np.abs(y - np.round(y))


def gen_term(x, k):
    """Generation-k contribution: tents of height 2**-k over its midpoints."""
    return 2.0 ** (-k) * tent((2.0 ** k) * x)


def takagi(x, n):
    """Finite Takagi approximation T_n = sum_{k=0}^{n} gen_term."""
    return sum(gen_term(x, k) for k in range(n + 1))


# ----------------------------------------------------------------------------
# Panel 1 — the resolution hierarchy: self-similar tents per generation
# ----------------------------------------------------------------------------
def draw_tents(ax, nmax=6):
    x = np.linspace(0, 1, 2 ** 13 + 1)
    cmap = plt.get_cmap("viridis")
    for k in range(nmax + 1):
        ax.plot(x, gen_term(x, k), color=cmap(k / nmax), lw=1.4,
                label=f"gen {k+1}  (height 2^-{k})")
    # mark the first few relation-points at their tent peaks
    for label, xv, k in [("c", 0.5, 0), ("d", 0.25, 1), ("e", 0.75, 1)]:
        yv = 2.0 ** (-k) * 0.5
        ax.scatter([xv], [yv], s=70, color="0.1", zorder=5)
        ax.text(xv, yv + 0.015, label, ha="center", fontsize=10,
                fontweight="bold")
    ax.set_title(
        "stage n = a resolution hierarchy\n"
        "each generation bridges its gaps with a tent of height 2^-k (self-similar)",
        fontsize=11)
    ax.set_xlabel("position on a—b", fontsize=9)
    ax.set_ylabel("bridging height (resolution)", fontsize=9)
    ax.legend(fontsize=7, loc="upper right", framealpha=0.9)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


# ----------------------------------------------------------------------------
# Panel 2 — the accumulated shape: finite Takagi -> blancmange fractal
# ----------------------------------------------------------------------------
def draw_takagi(ax):
    x = np.linspace(0, 1, 2 ** 14 + 1)
    cmap = plt.get_cmap("magma")
    stages = [1, 3, 5, 8, 13]
    for i, n in enumerate(stages):
        col = cmap(0.15 + 0.7 * i / (len(stages) - 1))
        ax.plot(x, takagi(x, n), color=col, lw=1.1 if n < 13 else 1.4,
                label=f"T_{n}", alpha=0.9)
    ax.set_title(
        "accumulated shape at stage n  =  finite Takagi (blancmange)\n"
        "continuous, nowhere differentiable, self-similar — the limit would flatten this away",
        fontsize=11)
    ax.set_xlabel("position on a—b", fontsize=9)
    ax.set_ylabel("accumulated between-displacement", fontsize=9)
    ax.legend(fontsize=8, loc="upper right", ncol=2, framealpha=0.9)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


def main():
    fig, axes = plt.subplots(1, 2, figsize=(16, 6.5))
    fig.patch.set_facecolor("white")
    draw_tents(axes[0])
    draw_takagi(axes[1])
    fig.suptitle(
        "the shape at an intermediate stage of between-pointing "
        "(where structure lives — the limit erases it)",
        fontsize=13, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    out = "research-notes/geometric/intermediate_shape.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
