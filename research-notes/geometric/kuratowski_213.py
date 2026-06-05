"""The 213 atomic signature sits on the planarity boundary (Kuratowski).

Kuratowski / Wagner: a graph is planar iff it has no K_5 or K_{3,3} minor.  The two
forbidden graphs are exactly 213 numbers:

  · K_n is planar  ⟺  n ≤ 4.   So d = N_S + N_T = 5 makes K_5 the FIRST non-planar
    complete graph — d = (planar ceiling 4) + 1.  K_5 is the 4-simplex skeleton.
  · K_{m,n} is planar  ⟺  min(m,n) ≤ 2.   213 has N_T = 2, so the canonical lattice
    K_{3,2} = K_{N_S,N_T} is the LAST planar complete bipartite graph; bumping
    N_T → N_S (the det=0 degenerate K_{3,3} of Mobius213K33Bridge) is the FIRST
    non-planar one.  N_T = 2 is *exactly* the bipartite planarity ceiling.

So the shapeLens (complete reading) leaves the plane precisely at the atomic
count; the dimension-Lens demand (the simplex wants d−1 dimensions) is the same
fact.  Whether this is deep structure or small-number coincidence is flagged
honestly: N_T = 2 = the K_{m,n} planarity bound is an exact equality (suggestive);
d = 5 = ceiling + 1 is one-off.

Run:  python3 research-notes/geometric/kuratowski_213.py
"""

import numpy as np
import matplotlib.pyplot as plt


def edges_complete(pos, ax, color="#3b6fb0"):
    n = len(pos)
    for i in range(n):
        for j in range(i + 1, n):
            ax.plot([pos[i][0], pos[j][0]], [pos[i][1], pos[j][1]],
                    color=color, lw=1.2, alpha=0.7, zorder=1)


def draw_nodes(ax, pos, cols=None):
    P = np.array(pos)
    ax.scatter(P[:, 0], P[:, 1], s=110,
               color=(cols if cols else "0.15"), zorder=3,
               edgecolors="white", linewidths=1.3)
    ax.set_aspect("equal"); ax.axis("off")


def main():
    fig, ax = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor("white")

    # K_4 — planar (triangle + center)
    a = ax[0, 0]
    p4 = [(0, 1), (-0.87, -0.5), (0.87, -0.5), (0, 0)]
    edges_complete(p4, a); draw_nodes(a, p4)
    a.set_title("K_4 — PLANAR (n ≤ 4)\nthe 3-simplex skeleton; fits the plane",
                fontsize=10.5)

    # K_5 — non-planar (circular, 1 forced crossing)
    b = ax[0, 1]
    th = np.linspace(0, 2 * np.pi, 5, endpoint=False) + np.pi / 2
    p5 = [(np.cos(t), np.sin(t)) for t in th]
    edges_complete(p5, b, "#d1495b"); draw_nodes(b, p5)
    b.set_title("K_5 — NON-PLANAR (n = 5 = d)\nfirst non-planar; 4-simplex skeleton",
                fontsize=10.5)

    # K_{3,2} — planar (theta: 2 poles, 3 disjoint middle paths)
    c = ax[1, 0]
    poles = [(-1.1, 0), (1.1, 0)]            # the N_T = 2 side
    mids = [(0, 0.8), (0, 0), (0, -0.8)]     # the N_S = 3 side
    for m in mids:
        for q in poles:
            c.plot([m[0], q[0]], [m[1], q[1]], color="#3b6fb0", lw=1.2,
                   alpha=0.7, zorder=1)
    draw_nodes(c, poles, "#2a9d6f"); draw_nodes(c, mids)
    c.set_title("K_{3,2} = K_{N_S,N_T} — PLANAR (min = N_T = 2)\n"
                "the canonical 213 lattice; last planar bipartite", fontsize=10.5)

    # K_{3,3} — non-planar (the det=0 degenerate; circular bipartite, crossings)
    d = ax[1, 1]
    top = [(-1, 0.9), (0, 0.9), (1, 0.9)]
    bot = [(-1, -0.9), (0, -0.9), (1, -0.9)]
    for t in top:
        for q in bot:
            d.plot([t[0], q[0]], [t[1], q[1]], color="#d1495b", lw=1.0,
                   alpha=0.6, zorder=1)
    draw_nodes(d, top); draw_nodes(d, bot)
    d.set_title("K_{3,3} — NON-PLANAR (min = 3)\nthe det=0 degenerate (K33Bridge); "
                "first non-planar bipartite", fontsize=10.5)

    fig.suptitle("The 213 atomic signature sits on the planarity boundary: "
                 "N_T = 2 = bipartite ceiling,  d = 5 = complete ceiling + 1",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.012,
             "K_n planar ⟺ n≤4 (so d=5 is the first non-planar K);  K_{m,n} planar "
             "⟺ min≤2=N_T (so K_{3,2} is the last planar bipartite, K_{3,3} the "
             "first non-planar).  The shapeLens leaves the plane exactly at the "
             "atomic numbers — the dimension-Lens demand, made topological.",
             ha="center", fontsize=9.5, color="0.3")
    fig.tight_layout(rect=[0, 0.03, 1, 0.95])
    out = "research-notes/geometric/kuratowski_213.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
