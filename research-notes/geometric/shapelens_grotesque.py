"""When does the shapeLens shape get grotesque? — the real cycle jumps.

Adding one point at a time (K_5, K_6, K_7, …) is ONE chosen linear path through the
exploding multi-axis lattice — possible only because a single axis was picked.  The
real cycle is a synchronous jump: every new line of the previous cycle spawns a
point at once.  Point counts:

    2 → 3 → 5 → 12 → 68 → 2280 → 2 598 062 → …    (n_{k+1} ≈ C(n_k,2) ≈ n_k²/2)

So a single natural-number "cycle" is clean only up to ~5 (= K_5, the planar
threshold); past that the count squares each cycle.  Where does it become
grotesque?
  · 5  (K_5):  10 lines — the last clean cycle number; first non-planar.
  · 12 (K_12): 66 lines, 150 crossings — already a mesh.
  · 68 (K_68): 2278 lines, ~333 000 crossings — an OPAQUE disk: grotesque.
  · 2280:      ~2.6 million lines — solid black, beyond any rendering.

So "막 폭발" arrives at the 4th cycle, 68 points: the first genuinely unrenderable
shape, two cycles past the planar threshold.

Run:  python3 research-notes/geometric/shapelens_grotesque.py
"""

import numpy as np
import matplotlib.pyplot as plt
from math import comb


def crossing_number(n):
    f = lambda m: m // 2
    return (f(n) * f(n - 1) * f(n - 2) * f(n - 3)) // 4


def draw_Kn(ax, n, lw, alpha, label):
    th = np.linspace(0, 2 * np.pi, n, endpoint=False) + np.pi / 2
    P = np.column_stack([np.cos(th), np.sin(th)])
    segs_x, segs_y = [], []
    for i in range(n):
        for j in range(i + 1, n):
            segs_x += [P[i, 0], P[j, 0], None]
            segs_y += [P[i, 1], P[j, 1], None]
    ax.plot(segs_x, segs_y, color="#3b6fb0", lw=lw, alpha=alpha, zorder=1)
    ax.scatter(P[:, 0], P[:, 1], s=max(2, 700 // n), color="0.1", zorder=3)
    ax.set_aspect("equal"); ax.set_xlim(-1.2, 1.2); ax.set_ylim(-1.2, 1.2)
    ax.axis("off")
    ax.set_title(label, fontsize=10.5)


def main():
    fig, axes = plt.subplots(2, 2, figsize=(15, 13))
    fig.patch.set_facecolor("white")

    draw_Kn(axes[0, 0], 5, 1.0, 0.6,
            "K_5  (cycle →5):  10 lines, ≥1 crossing\nthe last clean cycle number; first non-planar")
    draw_Kn(axes[0, 1], 12, 0.6, 0.5,
            "K_12 (cycle →12):  66 lines, ≥150 crossings\nalready a mesh")
    draw_Kn(axes[1, 0], 68, 0.15, 0.25,
            "K_68 (cycle →68):  2278 lines, ≈333 000 crossings\nGROTESQUE — an opaque disk")

    # explosion curve
    g = axes[1, 1]
    ns = [2, 3, 5, 12, 68, 2280, 2598062]
    k = list(range(len(ns)))
    g.semilogy(k, ns, "o-", color="#d1495b", lw=2)
    for kk, v in zip(k, ns):
        g.annotate(f"{v:,}", (kk, v), textcoords="offset points", xytext=(5, 5),
                   fontsize=9, color="0.3")
    g.axhspan(1, 100, color="#2a9d6f", alpha=0.08)
    g.text(0.1, 30, "renderable", color="#2a9d6f", fontsize=9)
    g.axhline(100, color="0.7", ls="--", lw=1)
    g.text(5.7, 200, "beyond\nrendering", color="0.5", fontsize=9, ha="right")
    g.set_title("the real cycle jumps: n_{k+1} ≈ n_k²/2  (doubly exponential)\n"
                "single-ℕ cycle clean only to 5; grotesque at 68; solid at 2280",
                fontsize=10.5)
    g.set_xlabel("cycle k", fontsize=9); g.set_ylabel("points (log)", fontsize=9)
    g.set_xticks(k)
    for s in ("top", "right"):
        g.spines[s].set_visible(False)

    fig.suptitle("When does the shapeLens get grotesque?  The cycle squares the "
                 "point count: 5 → 12 → 68 → 2280 → 2.6M",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.012,
             "one-at-a-time (K_5,6,7,…) is a chosen linear path through the exploding "
             "axes; the real cycle jumps 5→12→68→2280.  Grotesque (opaque, ~333k "
             "crossings) arrives at 68 — the 4th cycle, two past the planar threshold.",
             ha="center", fontsize=9.5, color="0.3")
    fig.tight_layout(rect=[0, 0.03, 1, 0.95])
    out = "research-notes/geometric/shapelens_grotesque.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
