"""Dimension-raising reading of the relation construction.

Mingu Jeong's first line is the hard constraint: "different objects are
different symbols."  Read literally (freely), a new relation-object is NOT
expressible as any combination of existing ones — it opens a NEW direction.

The midpoint reading violated this: c = (a+b)/2 identifies c with a real
combination of a,b, a quotient on the symbols.  Enough such relations collapse
the "between" into one homogeneous blob (structurally a point — the degenerate
limit).  Removing the quotient is the whole correction:

    relation(x,y) is NOT between x,y; it opens a fresh orthogonal axis, and the
    relation fills the simplex {x, y, relation(x,y)} (convex hull = continuum).

Then dimension grows with every object:
    a,b           -> 1-simplex (segment),    dim 1
    + c           -> 2-simplex (triangle),   dim 2
    + d           -> 3-simplex (tetrahedron),dim 3
    ...
    n objects     -> (n-1)-simplex
    limit n->inf  -> the infinite-dimensional simplex  Δ^∞,
                     an infinite-dimensional contractible continuum.

Crucially the vertices stay DISTINGUISHED: each free generator is a corner that
no convex combination of the others ever reaches, so distinctions survive the
limit -- it does not collapse to a point.  (213: the corners are the free
symbols; betweenness never reaches them, cf. object1_not_surjective.)

Run:  python3 research-notes/geometric/dimension_growth.py
"""

import numpy as np
import matplotlib.pyplot as plt
from itertools import combinations
from mpl_toolkits.mplot3d.art3d import Poly3DCollection


# ----------------------------------------------------------------------------
# Panel 1 — the dimension ladder: each object opens a new axis (3D up to dim 3)
# ----------------------------------------------------------------------------
def draw_ladder(ax):
    # regular tetrahedron: a,b (segment) -> +c (triangle) -> +d (tetrahedron)
    V = {
        "a": np.array([1.0, 1.0, 1.0]),
        "b": np.array([1.0, -1.0, -1.0]),
        "c": np.array([-1.0, 1.0, -1.0]),
        "d": np.array([-1.0, -1.0, 1.0]),
    }
    cmap = plt.get_cmap("viridis")
    cols = {"a": "0.15", "b": "0.15", "c": cmap(0.45), "d": cmap(0.8)}

    # filled faces of the tetrahedron (the simplices being filled in)
    faces = [("a", "b", "c"), ("a", "b", "d"), ("a", "c", "d"), ("b", "c", "d")]
    poly = Poly3DCollection(
        [[V[u] for u in f] for f in faces],
        alpha=0.13, facecolor=cmap(0.6), edgecolor="none")
    ax.add_collection3d(poly)

    # all edges = relations
    for u, w in combinations(V, 2):
        p, q = V[u], V[w]
        ax.plot(*zip(p, q), color="0.4", lw=1.4, alpha=0.7)

    for name, p in V.items():
        ax.scatter(*p, s=240, color=cols[name], edgecolors="white",
                   linewidths=1.2, depthshade=False)
        ax.text(*(p * 1.18), name, fontsize=13, fontweight="bold", ha="center")

    # the next object (e) gestured into the 4th dimension
    ax.text(0, 0, -2.1, "+e → 4-simplex → … → Δ^∞\n(new object = new axis)",
            fontsize=9, ha="center", color="0.3")

    ax.set_title("each new object opens a new dimension\n"
                 "a,b→segment  +c→triangle  +d→tetrahedron  (filled = continuum)",
                 fontsize=11)
    ax.set_box_aspect((1, 1, 1))
    ax.set_axis_off()
    ax.view_init(elev=18, azim=35)


# ----------------------------------------------------------------------------
# Panel 2 — the limit object: the infinite-dimensional simplex Δ^∞
# ----------------------------------------------------------------------------
def draw_infinite_simplex(ax, n=22):
    th = np.linspace(0, 2 * np.pi, n, endpoint=False) + np.pi / 2
    P = np.column_stack([np.cos(th), np.sin(th)])
    cmap = plt.get_cmap("viridis")

    # every pair is a relation -> the complete 1-skeleton of the n-1 simplex
    for i, j in combinations(range(n), 2):
        ax.plot([P[i, 0], P[j, 0]], [P[i, 1], P[j, 1]],
                color=cmap((i + j) / (2 * n)), lw=0.4, alpha=0.35, zorder=1)
    for i in range(n):
        ax.scatter(*P[i], s=130, color=cmap(i / n), edgecolors="white",
                   linewidths=1.0, zorder=3)
    labels = "abcdefghijklmnopqrstuvwxyz"
    for i in range(min(n, len(labels))):
        ax.text(P[i, 0] * 1.12, P[i, 1] * 1.12, labels[i], ha="center",
                va="center", fontsize=9, fontweight="bold")

    ax.set_title(
        "the limit:  the infinite-dimensional simplex  Δ^∞\n"
        "every symbol = a distinguished corner; betweenness never reaches it → no collapse",
        fontsize=11)
    ax.set_aspect("equal")
    ax.set_xlim(-1.3, 1.3)
    ax.set_ylim(-1.3, 1.3)
    ax.axis("off")


def main():
    fig = plt.figure(figsize=(16, 7))
    fig.patch.set_facecolor("white")
    ax1 = fig.add_subplot(1, 2, 1, projection="3d")
    ax2 = fig.add_subplot(1, 2, 2)
    draw_ladder(ax1)
    draw_infinite_simplex(ax2)

    fig.text(0.5, 0.03,
             "dimension per object:  2→dim 1 → 3→dim 2 → 4→dim 3 → … → n→dim (n−1) → ∞   "
             "(quotient removed: different symbols = independent axes)",
             ha="center", fontsize=10.5, color="0.3")
    fig.suptitle(
        "different objects = different symbols  ⇒  each relation opens a new axis "
        "⇒  limit = infinite-dimensional continuum",
        fontsize=13, fontweight="bold")
    fig.tight_layout(rect=[0, 0.06, 1, 0.95])
    out = "research-notes/geometric/dimension_growth.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
