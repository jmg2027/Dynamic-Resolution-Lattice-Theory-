"""Two descriptions, one structure — and where they coincide (μF ≅ νF).

A structure can be stated two ways (the user's point, = 02_axiom.md §2.3
self-completion + §5.7 frozen/dynamic):

  · DYNAMIC (constructive, μF / initial algebra): "S is built — each line gives a
    point, each point draws its lines, …"   (a process from below)
  · STATIC (completed, νF / final coalgebra): "S is complete; in S every line has
    its point, every point its line-relations."   (a consistency / fixed point)

No external time prefers one (§5.7); and the two faces cannot be viewed at once,
so investigating means surveying both.  The good news for THIS structure: its two
faces coincide — it is a self-fixed-point (μF ≅ νF, Lambek), the
"describe = reconstruct" case (`MobiusSelfForm.self_reconstruction_master`).  Most
codomains do NOT coincide, and the gap is the residue (`object1_not_surjective`).

  · complete-graph / simplex reading: construction limit = completed-S = the same
    complete graph.  μF ≅ νF.
  · betweenness / midpoint reading: construction = the countable dyadic points;
    completion = the continuum segment.  μF (countable) ≠ νF (continuum); the gap
    is reached by none.

Run:  python3 research-notes/geometric/static_dynamic_duality.py
"""

import numpy as np
import matplotlib.pyplot as plt


def panel_coincide(ax):
    # complete graph: both descriptions point to the SAME object
    n = 7
    th = np.linspace(0, 2 * np.pi, n, endpoint=False) + np.pi / 2
    P = np.column_stack([np.cos(th), np.sin(th)]) * 0.5
    P[:, 1] += 0.0
    for i in range(n):
        for j in range(i + 1, n):
            ax.plot([P[i, 0], P[j, 0]], [P[i, 1], P[j, 1]],
                    color="#3b6fb0", lw=0.5, alpha=0.6, zorder=1)
    ax.scatter(P[:, 0], P[:, 1], s=45, color="0.15", zorder=3)
    ax.annotate("DYNAMIC (μF)\nbuild: line→point,\nconnect all",
                xy=(0, 0.55), xytext=(-1.15, 1.0), fontsize=9, color="#2a9d6f",
                ha="center",
                arrowprops=dict(arrowstyle="->", color="#2a9d6f"))
    ax.annotate("STATIC (νF)\ncompleted S: every line\nhas its point, every\npoint its relations",
                xy=(0, -0.55), xytext=(1.15, -1.05), fontsize=9, color="#d1495b",
                ha="center",
                arrowprops=dict(arrowstyle="->", color="#d1495b"))
    ax.text(0, -1.55, "μF ≅ νF — the two faces coincide (self-fixed-point)",
            ha="center", fontsize=10, color="0.15", fontweight="bold")
    ax.set_title("complete graph / simplex reading\n"
                 "construction = consistency — the Lambek-coincidence case",
                 fontsize=11)
    ax.set_xlim(-1.7, 1.7); ax.set_ylim(-1.8, 1.5); ax.set_aspect("equal"); ax.axis("off")


def panel_gap(ax):
    # betweenness: dynamic = dyadic points; static = continuum segment
    # dynamic (top): dyadic points up to level 5
    depth = 5
    xs = set([0.0, 1.0])
    cur = [0.0, 1.0]
    for _ in range(depth):
        nv = []
        s = sorted(xs)
        for a, b in zip(s[:-1], s[1:]):
            nv.append((a + b) / 2)
        xs.update(nv)
    pts = sorted(xs)
    ax.scatter(pts, [0.6] * len(pts), s=12, color="#2a9d6f", zorder=3)
    ax.text(0.5, 0.85, "DYNAMIC (μF): the countable dyadic points (the construction)",
            ha="center", fontsize=9, color="#2a9d6f")
    # static (bottom): solid continuum
    ax.plot([0, 1], [0.0, 0.0], color="#d1495b", lw=6, solid_capstyle="round",
            zorder=3)
    ax.text(0.5, -0.25, "STATIC (νF): the continuum segment [a,b] (the completion)",
            ha="center", fontsize=9, color="#d1495b")
    ax.annotate("", xy=(0.5, 0.05), xytext=(0.5, 0.55),
                arrowprops=dict(arrowstyle="<->", color="0.4", lw=1.2))
    ax.text(0.5, -0.6,
            "μF (countable) ≠ νF (continuum) — the gap is reached by none\n"
            "(object1_not_surjective); the two faces differ",
            ha="center", fontsize=10, color="0.15", fontweight="bold")
    ax.set_title("betweenness / midpoint reading\n"
                 "construction ≠ completion — the generic (hard) case",
                 fontsize=11)
    ax.set_xlim(-0.05, 1.05); ax.set_ylim(-0.85, 1.05); ax.axis("off")


def main():
    fig, ax = plt.subplots(1, 2, figsize=(15, 6.5))
    fig.patch.set_facecolor("white")
    panel_coincide(ax[0])
    panel_gap(ax[1])
    fig.suptitle("One structure, two descriptions (dynamic μF / static νF) — "
                 "they coincide for the simplex reading, differ for most",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "no external time prefers construction over completion (§5.7); the two "
             "cannot be viewed at once, so one surveys both.  The simplex reading is "
             "the self-fixed-point μF ≅ νF case — which is why it is tractable.",
             ha="center", fontsize=9.5, color="0.3")
    fig.tight_layout(rect=[0, 0.05, 1, 0.95])
    out = "research-notes/geometric/static_dynamic_duality.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
