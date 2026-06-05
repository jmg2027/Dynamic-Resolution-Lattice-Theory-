"""Geometric rendering of the *undirected* relation self-pointing.

Mingu Jeong's sketch: an object IS the relation of two distinct objects — the
new point that corresponds to the *line between* two points.  Start a, b; the
between-point of (a,b) is c; the between-points of (a,c),(c,b) are d,e; and so
on.  Every pair of points spawns a point, recursively, so the population grows
+1, +2, +4, +8, ... and its cardinality is left undetermined.

The relation is UNDIRECTED: relation(x,y) = relation(y,x).  Symmetry is the
whole content — a symmetric relation-point cannot sit off the segment without
choosing a side, and a side is an orientation.  So the relation-point lives
*between* its two parents (the symmetric choice = the midpoint).  Iterating
betweenness from two seeds therefore does not build a fractal; it fills in the
segment [a,b] densely.  The limit object is the line itself: dimension 1, the
in-between made of all the relation-points (the dyadic points, dense in [a,b]).

(213 note: sign / orientation is NOT a Raw primitive — it is a later reading the
difference-Lens lays on a *directed* pair, 06_lens_readings.md §6.7.  This
construction is one layer below that, pre-sign, hence symmetric.  Its number-
theoretic cousin is the mediant / Stern-Brocot tree, where the between-point of
two fractions is their mediant and iterating fills in all the rationals.)

Two panels:
  (1) the betweenness tree: every new point lands strictly between the two it
      relates — value on the x-axis, birth generation downward;
  (2) the limit: many generations of relation-points filling [a,b], converging
      to the solid segment.

Run:  python3 research-notes/geometric/object_as_relation.py
"""

import numpy as np
import matplotlib.pyplot as plt


# ----------------------------------------------------------------------------
# the construction: betweenness of adjacent points (the symmetric relation)
# ----------------------------------------------------------------------------
def build(generations):
    """Return points = list of (value, gen) and parents dict value -> (lo, hi).

    Seeds a=0, b=1.  Each generation inserts the midpoint of every adjacent
    pair currently on the line.  New-point counts: 1, 2, 4, 8, ...  (matches
    the sketch's +1, +2, +4, +8 explosion exactly).
    """
    vals = [0.0, 1.0]
    gen = {0.0: 0, 1.0: 0}
    parents = {}
    for g in range(1, generations + 1):
        new = []
        for lo, hi in zip(vals[:-1], vals[1:]):
            m = 0.5 * (lo + hi)
            gen[m] = g
            parents[m] = (lo, hi)
            new.append(m)
        vals = sorted(vals + new)
    return vals, gen, parents


# first letters, in birth order, for the labelled panel
LETTERS = "abcdefghijklmnopqrstuvwxyz"


def label_map(gen):
    order = sorted(gen, key=lambda v: (gen[v], v))
    return {v: LETTERS[i] for i, v in enumerate(order) if i < len(LETTERS)}


# ----------------------------------------------------------------------------
# Panel 1 — the betweenness tree (every node lands between its two parents)
# ----------------------------------------------------------------------------
def draw_tree(ax, gens=4):
    vals, gen, parents = build(gens)
    labels = label_map(gen)
    cmap = plt.get_cmap("viridis")
    maxg = gens

    # edges: each relation-point down to the two points it is between
    for m, (lo, hi) in parents.items():
        col = cmap(gen[m] / maxg)
        for p in (lo, hi):
            ax.plot([m, p], [-gen[m], -gen[p]], color=col, lw=1.1, alpha=0.5,
                    zorder=1)
    # nodes
    for v in vals:
        g = gen[v]
        col = "0.15" if g == 0 else cmap(g / maxg)
        ax.scatter([v], [-g], s=560 if g == 0 else 380, color=col,
                   edgecolors="white", linewidths=1.3, zorder=3)
        ax.text(v, -g, labels.get(v, ""), ha="center", va="center",
                color="white", fontsize=11 if g == 0 else 9,
                fontweight="bold", zorder=4)

    ax.set_title(
        "object = the point BETWEEN two objects (undirected)\n"
        r"$a,b \to c \to d,e \to \cdots$  —  no side, no orientation",
        fontsize=12)
    ax.set_xlim(-0.08, 1.08)
    ax.set_ylim(-maxg - 0.5, 0.6)
    ax.set_yticks([-g for g in range(maxg + 1)])
    ax.set_yticklabels([f"gen {g}" for g in range(maxg + 1)], fontsize=8)
    ax.set_xlabel("value (position on the line a—b)", fontsize=9)
    for s in ("top", "right", "left"):
        ax.spines[s].set_visible(False)
    ax.tick_params(left=False)


# ----------------------------------------------------------------------------
# Panel 2 — the limit: betweenness fills the segment [a,b]
# ----------------------------------------------------------------------------
def draw_limit(ax, gens=11):
    vals, gen, _ = build(gens)
    cmap = plt.get_cmap("magma")
    for v in vals:
        g = gen[v]
        ax.plot([v, v], [-g, 0.0], color=cmap(g / gens), lw=0.6, alpha=0.5,
                zorder=1)
        ax.scatter([v], [-g], s=max(4, 26 - 2.2 * g), color=cmap(g / gens),
                   zorder=2)
    # the completed continuum
    ax.plot([0, 1], [0.0, 0.0], color="0.1", lw=4, solid_capstyle="round",
            zorder=3)
    ax.scatter([0, 1], [0, 0], s=90, color="0.1", edgecolors="white",
               linewidths=1.2, zorder=4)
    ax.text(0, 0.25, "a", ha="center", fontsize=11, fontweight="bold")
    ax.text(1, 0.25, "b", ha="center", fontsize=11, fontweight="bold")
    ax.text(0.5, 0.55,
            "limit = the segment itself  (dimension 1 — the in-between, dense)",
            ha="center", fontsize=10, color="0.25")

    ax.set_title(
        "the limit of unbounded between-pointing\n"
        "every relation-point lands inside [a,b]; they fill it densely",
        fontsize=12)
    ax.set_xlim(-0.05, 1.05)
    ax.set_ylim(-gens - 0.5, 1.1)
    ax.axis("off")


def main():
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))
    fig.patch.set_facecolor("white")
    draw_tree(axes[0])
    draw_limit(axes[1])

    fig.text(0.5, 0.02,
             "new objects per generation:  +1 → +2 → +4 → +8 → ⋯   "
             "(cardinality undetermined)",
             ha="center", fontsize=11, color="0.3")
    fig.suptitle("an object IS the (undirected) relation of two distinct objects",
                 fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0.05, 1, 0.95])
    out = "research-notes/geometric/object_as_relation.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
