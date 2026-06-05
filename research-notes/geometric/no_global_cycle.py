"""No canonical global cycle number — the cycle index is a foliation (a Lens).

The user's challenge to conjecture 1: can a single natural number define the
global cycle?  No.  From cycle 2 the growth axes are independent, so:
  (1) bundling them into one "global cycle 2" is a choice (which side?);
  (2) processing one axis creates new lines mid-cycle, so the cycle has no clean
      boundary.

What is schedule-INVARIANT (by confluence) is the lattice of configurations — the
partial order of "what must precede what."  A "global cycle = n" numbering is a
foliation of that lattice into levels, i.e. a choice of synchronization barrier —
which needs an external clock the axiom does not provide (§5.1 no exterior, §6.2
no external time).  So it is exactly like relativity: the causal partial order is
invariant; a global simultaneity (the cycle slicing) is frame-dependent.

Illustration: the configuration lattice for two axes d, e (operations d<da, e<ea),
a 3×3 grid.  Two valid schedules (monotone paths ∅→top) pass through different
intermediate states — neither is "the" cycle 2.

Run:  python3 research-notes/geometric/no_global_cycle.py
"""

import numpy as np
import matplotlib.pyplot as plt


def main():
    fig, ax = plt.subplots(1, 2, figsize=(15, 6.8))
    fig.patch.set_facecolor("white")

    # configuration lattice: states (i,j), i = progress on d-axis (0,1,2),
    # j = progress on e-axis.  Hasse edges (i,j)->(i+1,j),(i,j+1).
    labels = {
        (0, 0): "∅", (1, 0): "d", (2, 0): "d,da",
        (0, 1): "e", (0, 2): "e,ea", (1, 1): "d,e",
        (2, 1): "d,da,e", (1, 2): "d,e,ea", (2, 2): "ALL",
    }
    a = ax[0]
    for (i, j) in labels:
        for (di, dj) in ((1, 0), (0, 1)):
            if (i + di, j + dj) in labels:
                a.plot([i, i + di], [j, j + dj], color="0.7", lw=1, zorder=1)
    # two schedules
    pathA = [(0, 0), (1, 0), (2, 0), (2, 1), (2, 2)]   # d-axis first
    pathB = [(0, 0), (0, 1), (0, 2), (1, 2), (2, 2)]   # e-axis first
    for path, col, lab in ((pathA, "#3b6fb0", "schedule A (d first)"),
                           (pathB, "#d1495b", "schedule B (e first)")):
        xs = [p[0] for p in path]; ys = [p[1] for p in path]
        a.plot(xs, ys, color=col, lw=3, alpha=0.6, zorder=2, label=lab)
    for (i, j), s in labels.items():
        a.scatter([i], [j], s=900, color="0.2", zorder=3)
        a.text(i, j, s, ha="center", va="center", color="white", fontsize=7.5,
               fontweight="bold", zorder=4)
    a.set_title("the configuration lattice (schedule-INVARIANT)\n"
                "two valid schedules slice 'cycle 2' differently — neither is canonical",
                fontsize=11)
    a.legend(fontsize=9, loc="upper left")
    a.set_xlim(-0.4, 2.4); a.set_ylim(-0.4, 2.4); a.axis("off")

    # the rank (op-count) is the only invariant grading — but it is antichains,
    # not cycles
    b = ax[1]
    for (i, j) in labels:
        for (di, dj) in ((1, 0), (0, 1)):
            if (i + di, j + dj) in labels:
                b.plot([i, i + di], [j, j + dj], color="0.85", lw=1, zorder=1)
    cmap = plt.get_cmap("viridis")
    for (i, j) in labels:
        b.scatter([i], [j], s=700, color=cmap((i + j) / 4), zorder=3,
                  edgecolors="white", linewidths=1)
        b.text(i, j, str(i + j), ha="center", va="center", color="white",
               fontsize=10, fontweight="bold", zorder=4)
    # antichain bands
    for r in range(5):
        pts = [(i, j) for (i, j) in labels if i + j == r]
        if len(pts) > 1:
            xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
            b.plot(xs, ys, color="#d1495b", lw=1, ls="--", alpha=0.5)
    b.set_title("the only invariant grading is op-count (rank)\n"
                "each level is an ANTICHAIN, not a state — 'global cycle' is a slice",
                fontsize=11)
    b.set_xlim(-0.4, 2.4); b.set_ylim(-0.4, 2.4); b.axis("off")

    fig.suptitle("No canonical global cycle number — the cycle index is a foliation "
                 "(a Lens / a frame), not intrinsic",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "confluence ⇒ the lattice (causal partial order) is invariant; a "
             "'global cycle = n' slicing is a synchronization barrier = a global "
             "simultaneity, frame-dependent, needing an external clock (§5.1, §6.2).",
             ha="center", fontsize=9.5, color="0.3")
    fig.tight_layout(rect=[0, 0.05, 1, 0.95])
    out = "research-notes/geometric/no_global_cycle.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
