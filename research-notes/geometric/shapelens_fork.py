"""The shapeLens secret: where single-ℕ counting forks — and it is d = 5.

The canonical (synchronous, choice-free-per-cycle) point/line generation produces
point counts  2, 3, 5, 12, 68, 2280, …  and new-points-per-cycle ("growth axes")
1, 2, 7, 56, 2212, ….

The structural event the user identified: the cycle is a SINGLE growth axis (one
new point) only while new-per-cycle = 1 — that is, only the step 2 → 3.  At 3 the
process forces +2 (two independent points d, e at once), so:

  · single-ℕ counting (n → n+1, the count-Lens unit) holds only 2 → 3; at 3 it is
    forced to JUMP +2 → 5.  The canonical sequence 2,3,5,12,68 SKIPS 4.
  · the fork (first ≥2 simultaneous axes) = the birth of genuine dimension:
    1 axis = 1-D = layable on a line = ℕ-orderable; ≥2 axes = a poset/lattice, no
    single ℕ index (the no-global-cycle finding).
  · planarity: the single-axis regime stays planar (K_3, a triangle); the +2 jump
    leaps the planar tetrahedron K_4 and lands on the FIRST non-planar K_5.

So three thresholds coincide at the same +2 jump (3 → 5):
  single-ℕ ends  =  planarity ends (K_4 skipped → K_5)  =  atomic d = 5.
A second, shapeLens-internal route to the atomic count: d = the first complete
graph the generation reaches by an irreducibly multi-axis (non-linear) step.

Run:  python3 research-notes/geometric/shapelens_fork.py
"""

import numpy as np
import matplotlib.pyplot as plt


def main():
    fig, ax = plt.subplots(1, 2, figsize=(16, 6.5))
    fig.patch.set_facecolor("white")

    # Panel A: the canonical count line, with 4 skipped, thresholds marked
    a = ax[0]
    counts = [2, 3, 5, 12, 68]
    a.plot(counts, [0] * len(counts), "o-", color="#3b6fb0", lw=1.6, ms=10, zorder=2)
    for c in counts:
        a.annotate(str(c), (c, 0), textcoords="offset points", xytext=(0, 10),
                   ha="center", fontsize=11, fontweight="bold")
    # mark 4 as skipped
    a.scatter([4], [0], s=140, facecolors="none", edgecolors="#d1495b", lw=2,
              zorder=3)
    a.annotate("4 SKIPPED\n(planar K_4 leapt)", (4, 0), textcoords="offset points",
               xytext=(0, -34), ha="center", fontsize=8.5, color="#d1495b")
    # regime brackets
    a.annotate("", xy=(3.1, 0.45), xytext=(1.9, 0.45),
               arrowprops=dict(arrowstyle="-", color="#2a9d6f", lw=2))
    a.text(2.5, 0.55, "single axis\n(forced, ℕ, planar)", ha="center", fontsize=9,
           color="#2a9d6f")
    a.annotate("", xy=(70, 0.45), xytext=(4.9, 0.45),
               arrowprops=dict(arrowstyle="-", color="#7a3bb0", lw=2))
    a.text(20, 0.55, "multi-axis\n(forked, beyond-ℕ, non-planar)", ha="center",
           fontsize=9, color="#7a3bb0")
    a.annotate("FORK = +2 jump\n3→5", (4, 0.0), textcoords="offset points",
               xytext=(8, 26), fontsize=9, color="#d1495b", fontweight="bold")
    a.set_xscale("log")
    a.set_xlim(1.7, 90); a.set_ylim(-0.7, 0.9)
    a.set_yticks([]); a.set_xticks([2, 3, 5, 12, 68])
    a.set_xticklabels(["2", "3", "5", "12", "68"])
    a.set_title("canonical point counts (log): 2, 3, 5, 12, 68 — 4 is skipped;\n"
                "single-ℕ ends, planarity ends, d=5 — one event (the 3→5 fork)",
                fontsize=10.5)
    for s in ("top", "right", "left"):
        a.spines[s].set_visible(False)

    # Panel B: growth axes per cycle (new points): 1, 2, 7, 56
    b = ax[1]
    axes_per = [1, 2, 7, 56, 2212]
    b.bar(range(len(axes_per)), axes_per, color=["#2a9d6f", "#d1495b", "#7a3bb0",
                                                 "#7a3bb0", "#7a3bb0"])
    b.set_yscale("log")
    for i, v in enumerate(axes_per):
        b.annotate(str(v), (i, v), textcoords="offset points", xytext=(0, 3),
                   ha="center", fontsize=9)
    b.axhline(1.5, color="0.6", ls="--", lw=1)
    b.text(3.6, 1.7, "axes > 1 ⟹ fork\n(no single ℕ)", fontsize=8.5, color="#d1495b",
           ha="right")
    b.set_title("growth axes per cycle (new points): 1, 2, 7, 56, …\n"
                "single axis only at cycle 1 (→3); the fork is at the cycle reaching 5",
                fontsize=10.5)
    b.set_xlabel("cycle", fontsize=9); b.set_ylabel("new points (log)", fontsize=9)
    b.set_xticks(range(len(axes_per)))
    for s in ("top", "right"):
        b.spines[s].set_visible(False)

    fig.suptitle("The shapeLens secret: where single-ℕ counting forks into "
                 "multi-dimensional explosion — and it is exactly d = 5",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.01,
             "ℕ-successor (the count-Lens unit, +1) generates only 2→3; at 3 the "
             "lens forces +2, skipping the planar K_4 and landing on the first "
             "non-planar / multi-axis / atomic K_5.  ℕ is the 1-axis (1-D) shadow; "
             "the lens is intrinsically multi-axis past d.",
             ha="center", fontsize=9.5, color="0.3")
    fig.tight_layout(rect=[0, 0.04, 1, 0.94])
    out = "research-notes/geometric/shapelens_fork.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
