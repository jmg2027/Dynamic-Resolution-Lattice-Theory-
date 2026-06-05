"""The shapeLens, drawn one step at a time, from 5 points.

The cleanest rule (Mingu Jeong): each line → a point, each new point joins every
point it is not yet connected to.  A single fine-grained step = "take a line, make
its point, connect it to all" = add one vertex joined to everyone = K_n → K_{n+1}.
So, starting from 5 points (= K_5), the step-by-step picture is K_5, K_6, K_7, …

Insights surfaced by actually drawing it (annotated on the panels):
  · the shape is ALWAYS the complete graph K_n — vertex-transitive, no landmark
    (every point looks alike), so adding points HOMOGENIZES → the limit has no
    internal structure (§6.5: K_∞ ≡ point).
  · three diverging rates: points ~ n, lines = C(n,2) ~ n²/2, min crossings
    cr(K_n) ~ n⁴/64.  The relational/visual content explodes far faster than the
    objects — "lines become points" with lines ≫ points is the explosion engine.
  · NON-PLANAR from exactly K_5 (Kuratowski): 5 points is the threshold where the
    shape leaves the plane; the 2-D crossing cost then grows like n⁴.  The complete
    graph "wants" the simplex's dimensions (the dimension-Lens) — the plane cannot
    hold it past K_4.
  · the two Kuratowski forbidden graphs are K_5 and K_{3,3} — both 213 numbers
    (5 = d; K_{3,3}/K_{3,2} the bipartite cell).  The planarity obstruction sits
    exactly at the atomic signature.

Run:  python3 research-notes/geometric/shapelens_stepwise.py
"""

import numpy as np
import matplotlib.pyplot as plt
from math import comb


def crossing_number(n):
    # Guy's formula (the conjectured/known optimal crossing number of K_n)
    f = lambda m: m // 2
    return (f(n) * f(n - 1) * f(n - 2) * f(n - 3)) // 4


def draw_Kn(ax, n, highlight_newest=False):
    th = np.linspace(0, 2 * np.pi, n, endpoint=False) + np.pi / 2
    P = np.column_stack([np.cos(th), np.sin(th)])
    for i in range(n):
        for j in range(i + 1, n):
            ax.plot([P[i, 0], P[j, 0]], [P[i, 1], P[j, 1]],
                    color="#3b6fb0", lw=0.5, alpha=0.45, zorder=1)
    ax.scatter(P[:, 0], P[:, 1], s=70, color="0.15", zorder=3, edgecolors="white",
               linewidths=1)
    if highlight_newest:
        ax.scatter(*P[-1], s=120, color="#d1495b", zorder=4, edgecolors="white",
                   linewidths=1.2)
    cr = crossing_number(n)
    tag = "  ← non-planar (Kuratowski)" if n == 5 else ""
    ax.set_title(f"K_{n}:  {n} points,  {comb(n,2)} lines,  ≥{cr} crossings{tag}",
                 fontsize=10.5)
    ax.set_aspect("equal"); ax.set_xlim(-1.25, 1.25); ax.set_ylim(-1.25, 1.25)
    ax.axis("off")


def main():
    fig, axes = plt.subplots(2, 3, figsize=(16, 11))
    fig.patch.set_facecolor("white")
    for ax, n in zip(axes.flat, [5, 6, 7, 8, 9, 10]):
        draw_Kn(ax, n, highlight_newest=(n > 5))
    fig.suptitle("The shapeLens, step by step from 5 points: each step adds one "
                 "point joined to all → K_5, K_6, K_7, …  (always the complete graph)",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.012,
             "points ~ n,  lines = C(n,2) ~ n²/2,  crossings ~ n⁴/64 — the shape "
             "homogenizes (vertex-transitive, no landmark) and leaves the plane at "
             "K_5; it 'wants' the simplex's dimensions.",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.03, 1, 0.95])
    out = "research-notes/geometric/shapelens_stepwise.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)
    # console: the three diverging rates
    print("n   points  lines=C(n,2)  cr(K_n)")
    for n in range(5, 13):
        print(f"{n:<3} {n:<7} {comb(n,2):<13} {crossing_number(n)}")


if __name__ == "__main__":
    main()
