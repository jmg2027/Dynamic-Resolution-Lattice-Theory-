"""The 'line ↔ point, connect to all non-connected' rule → the complete graph.

Mingu Jeong's refined cycle:
  · two points;
  · draw the line(s) between points          (중간 1)
  · each line corresponds to one new point    (중간 2 — line ↔ point = the slash)
  · the new point draws lines to every point it is NOT already connected to (중간 3)
  · repeat: each new line → a point, each new point → lines to all non-connected.

What graph is this?  Computed exactly: at EVERY stage the graph is the complete
graph K_n (every vertex ends adjacent to every other, because a new vertex
connects to all then-existing, and all later vertices connect back to it).  The
"이어지지 않은" (only non-already-connected) clause is exactly what keeps it a
simple graph and is the reason it is not a tree — it is the *maximally* not-a-tree
object: K_n.

  point counts   n_k :  2, 3, 5, 12, 68, 2280, ~2.6·10⁶, …
  new per round       :  1, 2, 7, 56, 2212, …   (= new edges of the previous round)
  recursion           :  n_{k+1} = n_k + [C(n_k,2) − C(n_{k-1},2)],  graph = K_{n_k}
  growth              :  n_{k+1} ≈ C(n_k,2) ≈ n_k²/2  →  doubly exponential.

This lands exactly on the free / dimension-Lens cell: K_n is the 1-skeleton of the
regular (n−1)-simplex, so the limit is K_ω = Δ^∞
(`AngleStructure/SimplexOrthogonality.lean`).  "line → point" is the slash
(relation → object); "connect to all" is the free reading (every pair distinct and
adjacent).  It is the opposite end of the connection-criterion dial from the
sparse parent-edge graph; the user's rule picks the *complete* end.

Run:  python3 research-notes/geometric/complete_graph_rule.py
"""

import numpy as np
import matplotlib.pyplot as plt
from math import comb


def draw_complete(ax, n, title):
    th = np.linspace(0, 2 * np.pi, n, endpoint=False) + np.pi / 2
    P = np.column_stack([np.cos(th), np.sin(th)])
    for i in range(n):
        for j in range(i + 1, n):
            ax.plot([P[i, 0], P[j, 0]], [P[i, 1], P[j, 1]],
                    color="#3b6fb0", lw=0.4, alpha=0.5)
    ax.scatter(P[:, 0], P[:, 1], s=40, color="0.15", zorder=3)
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title(title, fontsize=10)


def main():
    # the exact sequence
    ns = [2]
    prev_edges = 0
    for _ in range(6):
        e = comb(ns[-1], 2)
        new = e - prev_edges
        ns.append(ns[-1] + new)
        prev_edges = e
    # ns = [2,3,5,12,68,2280,2598062,...]

    fig, ax = plt.subplots(2, 3, figsize=(16, 10))
    fig.patch.set_facecolor("white")

    draw_complete(ax[0, 0], 3, "after round 1: K₃  (n=3)")
    draw_complete(ax[0, 1], 5, "after round 2: K₅  (n=5)")
    draw_complete(ax[0, 2], 12, "after round 3: K₁₂  (n=12)")

    # growth
    g = ax[1, 0]
    k = np.arange(len(ns))
    g.semilogy(k, ns, "o-", color="#d1495b", lw=1.6)
    for kk, v in zip(k, ns):
        g.annotate(str(v), (kk, v), textcoords="offset points", xytext=(4, 4),
                   fontsize=8, color="0.3")
    g.set_title("growth: n_{k+1} = n_k + [C(n_k,2) − C(n_{k-1},2)]\n"
                "≈ n_k²/2 per round — doubly exponential", fontsize=10)
    g.set_xlabel("round k", fontsize=9); g.set_ylabel("points n_k (log)", fontsize=9)
    for s in ("top", "right"):
        g.spines[s].set_visible(False)

    # edge<->vertex correspondence (new points per round = new lines prev round)
    c = ax[1, 1]
    newpts = [ns[i + 1] - ns[i] for i in range(len(ns) - 1)]
    c.bar(range(len(newpts)), newpts, color="#2a9d6f")
    c.set_yscale("log")
    for i, v in enumerate(newpts):
        c.annotate(str(v), (i, v), textcoords="offset points", xytext=(0, 3),
                   ha="center", fontsize=8, color="0.3")
    c.set_title("line ↔ point: new points per round\n"
                "= new lines of the previous round (1, 2, 7, 56, 2212, …)",
                fontsize=10)
    c.set_xlabel("round", fontsize=9); c.set_ylabel("new points (log)", fontsize=9)
    for s in ("top", "right"):
        c.spines[s].set_visible(False)

    # tie to the simplex: K_5 = 1-skeleton of the 4-simplex
    draw_complete(ax[1, 2], 5,
                  "K_n = 1-skeleton of the (n−1)-simplex\n"
                  "limit K_ω = Δ^∞ (the free / dimension-Lens cell)")

    fig.suptitle("'each line becomes a point, each point joins all non-connected' "
                 "→ the complete graph K_n → the simplex Δ^∞",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "confirmed: the graph is exactly K_n at every stage (the maximally "
             "not-a-tree object).  'line→point' = the slash; 'connect to all' = the "
             "free reading; the shape it builds toward is the infinite simplex.",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.045, 1, 0.95])
    out = "research-notes/geometric/complete_graph_rule.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out, "| n_k =", ns)


if __name__ == "__main__":
    main()
