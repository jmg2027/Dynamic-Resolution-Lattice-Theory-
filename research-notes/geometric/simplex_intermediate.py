"""The shape at an intermediate stage of the dimension-raising (free) reading.

After n+1 objects the free construction is a regular n-simplex (every pair of
symbols equidistant, every symbol a corner).  This is the finite-resolution
object; the limit is Delta^infinity.  As n grows the regular n-simplex changes
shape by exact laws -- the analogue of the Takagi/ruler signature found for the
betweenness construction.

Closed forms (regular n-simplex, unit edge, n+1 vertices, dimension n):

  centroid pairwise angle   theta(n) = arccos(-1/n)        -> 90 deg
  dihedral angle            delta(n) = arccos( 1/n)        -> 90 deg
  inradius / circumradius   r/R      = 1/n                 -> 0
  volume (unit edge)        V(n)     = sqrt(n+1)/(n! 2^{n/2}) -> 0  (super-exp.)
  edge-edge angle at vertex = 60 deg  (every 3 vertices equilateral; n-invariant)

Anchors:  n=2 triangle -> centroid 120 deg, dihedral 60 deg
          n=3 tetra    -> centroid 109.47 deg (tetrahedral angle), dihedral 70.53

Reading: the corners spread to mutual orthogonality (centroid angle -> 90), i.e.
the free symbols become an orthonormal set (the basis e_i of Delta^infty in ell^2);
meanwhile the body thins to nothing (r/R -> 0, V -> 0).  This is concentration of
measure / the curse of dimensionality: the n-simplex becomes "all corners, no
middle."  Independence of the symbols is reached only in the limit, approached
monotonically -- the intermediate stage measures how far along that climb it is.

Run:  python3 research-notes/geometric/simplex_intermediate.py
"""

import numpy as np
import matplotlib.pyplot as plt
from math import factorial


def descriptors(nmax=40):
    n = np.arange(2, nmax + 1, dtype=float)
    centroid = np.degrees(np.arccos(-1.0 / n))
    dihedral = np.degrees(np.arccos(1.0 / n))
    r_over_R = 1.0 / n
    vol = np.array([np.sqrt(k + 1) / (factorial(int(k)) * 2.0 ** (k / 2.0))
                    for k in n])
    return n, centroid, dihedral, r_over_R, vol


# ----------------------------------------------------------------------------
# Panel 1 — the angles climb to 90 deg: corners spread to orthogonality
# ----------------------------------------------------------------------------
def draw_angles(ax, n, centroid, dihedral):
    ax.axhline(90, color="0.6", ls="--", lw=1, zorder=0)
    ax.text(n[-1], 90.8, "90°  (orthogonal: vertices → orthonormal basis)",
            ha="right", fontsize=9, color="0.4")
    ax.plot(n, centroid, "o-", ms=3, color="#3b6fb0", lw=1.5,
            label=r"centroid pairwise angle  $\arccos(-1/n)$")
    ax.plot(n, dihedral, "s-", ms=3, color="#c0573b", lw=1.5,
            label=r"dihedral angle  $\arccos(1/n)$")
    # anchors
    for xv, yv, txt in [(2, 120, "120°\n(triangle)"),
                        (3, 109.47, "109.47°\n(tetrahedral)"),
                        (2, 60, "60°\n(triangle dihedral)"),
                        (3, 70.53, "70.53°\n(tetra dihedral)")]:
        ax.scatter([xv], [yv], s=45, color="0.1", zorder=5)
        ax.annotate(txt, (xv, yv), textcoords="offset points",
                    xytext=(8, -2 if yv < 90 else 6), fontsize=7.5, color="0.3")
    ax.set_title("intermediate n-simplex: every angle climbs to 90°\n"
                 "the free corners spread to mutual orthogonality", fontsize=11)
    ax.set_xlabel("n  (dimension of the intermediate simplex)", fontsize=9)
    ax.set_ylabel("angle (degrees)", fontsize=9)
    ax.legend(fontsize=8, loc="center right")
    ax.set_ylim(50, 130)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


# ----------------------------------------------------------------------------
# Panel 2 — the body thins to nothing: spikiness + vanishing volume
# ----------------------------------------------------------------------------
def draw_thinness(ax, n, r_over_R, vol):
    ax.plot(n, r_over_R, "o-", ms=3, color="#2a9d6f", lw=1.5,
            label=r"inradius / circumradius $= 1/n$")
    ax.set_xlabel("n  (dimension of the intermediate simplex)", fontsize=9)
    ax.set_ylabel("inradius / circumradius", color="#2a9d6f", fontsize=9)
    ax.tick_params(axis="y", labelcolor="#2a9d6f")
    ax.set_ylim(0, 0.55)
    ax.text(n[-1], 0.02, "→ 0  (all corners, no middle)", ha="right",
            fontsize=9, color="#2a9d6f")

    ax2 = ax.twinx()
    ax2.semilogy(n, vol, "^-", ms=3, color="#7a3bb0", lw=1.5,
                 label="volume (unit edge)")
    ax2.set_ylabel("regular n-simplex volume  (log)", color="#7a3bb0",
                   fontsize=9)
    ax2.tick_params(axis="y", labelcolor="#7a3bb0")

    ax.set_title("intermediate n-simplex: the body vanishes\n"
                 "concentration of measure — the curse of dimensionality",
                 fontsize=11)
    for s in ("top",):
        ax.spines[s].set_visible(False)
        ax2.spines[s].set_visible(False)
    # combined legend
    l1, lab1 = ax.get_legend_handles_labels()
    l2, lab2 = ax2.get_legend_handles_labels()
    ax.legend(l1 + l2, lab1 + lab2, fontsize=8, loc="upper right")


def main():
    n, centroid, dihedral, r_over_R, vol = descriptors(40)
    fig, axes = plt.subplots(1, 2, figsize=(16, 6.2))
    fig.patch.set_facecolor("white")
    draw_angles(axes[0], n, centroid, dihedral)
    draw_thinness(axes[1], n, r_over_R, vol)
    fig.suptitle(
        "intermediate-stage shape of the free construction: the regular n-simplex "
        "spreads to orthogonality and thins to nothing",
        fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "limit: vertices → orthonormal (pairwise 90°), body → measure zero. "
             "Independence is reached only at ∞ — the stage n measures the climb.",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.05, 1, 0.95])
    out = "research-notes/geometric/simplex_intermediate.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
