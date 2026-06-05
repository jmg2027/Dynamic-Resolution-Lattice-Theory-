"""K4 breadth — the de Rham w-family: many shapes from one parameter.

The directed off-segment reading of the slash is the de Rham recursion
relation(x, y) = x + (y − x)·w, recurse on (x, p) and (p, y).  Sweeping the one
complex parameter w gives a whole family of self-similar curves — Cesàro/Koch,
Lévy, and everything between — the breadth side of the slash-reading atlas.

Honest frontier line: the SHAPE is one dial, but the *fractal dimension* of each
curve is the non-∅-axiom edge.  The similarity dimension solves the Moran
equation |w|^d + |1−w|^d = 1 (shown per panel); the true Hausdorff dimension is
below it wherever the two sub-copies overlap (e.g. the Lévy curve), and neither
has a Real213 ∅-axiom shadow yet.

The OTHER half of K4 — "which other SL(2,ℤ) generators yield 213 numbers" — IS
∅-axiom: the metallic generator tower N_k = [[k,1],[1,0]] (det = −1 ∀k), with the
213 golden the minimal disc = d = 5 rung and N_1² = P, in
`lean/E213/Lib/Math/Algebra/Mobius213/Px/MetallicGeneratorTower.lean`.

Run:  python3 research-notes/geometric/derham_family.py
"""

import numpy as np
import matplotlib.pyplot as plt
from math import log


def derham(w, depth):
    """Polyline of the de Rham curve for parameter w (complex), from 0 to 1."""
    pts = [0 + 0j, 1 + 0j]
    for _ in range(depth):
        new = []
        for x, y in zip(pts[:-1], pts[1:]):
            new.append(x)
            new.append(x + (y - x) * w)
        new.append(pts[-1])
        pts = new
    return np.array(pts)


def moran_dim(w):
    """Similarity dimension: d with |w|^d + |1−w|^d = 1 (bisection)."""
    r1, r2 = abs(w), abs(1 - w)
    if r1 >= 1 or r2 >= 1:
        return float("nan")
    lo, hi = 0.0, 8.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if r1 ** mid + r2 ** mid > 1:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


# a sweep across the family, plus the name where it is classical
PARAMS = [
    (0.5 + 0.10j, "near-flat"),
    (0.5 + 0.2887j, "Cesàro–Koch"),
    (0.5 + 0.40j, "Cesàro"),
    (0.5 + 0.50j, "Lévy C"),
    (0.5 + 0.65j, "Lévy-ish"),
    (0.30 + 0.30j, "asymmetric"),
]


def main():
    fig, axes = plt.subplots(2, 3, figsize=(16, 8.5))
    fig.patch.set_facecolor("white")
    cmap = plt.get_cmap("magma")
    for ax, (w, name) in zip(axes.flat, PARAMS):
        pts = derham(w, 14)
        xs, ys = pts.real, pts.imag
        seg = np.linspace(0, 1, len(xs))
        ax.scatter(xs, ys, c=seg, cmap=cmap, s=0.4)
        ax.plot(xs, ys, color="0.6", lw=0.2, alpha=0.5)
        d = moran_dim(w)
        ax.set_title(f"w = {w.real:.3g}+{w.imag:.3g}i   ({name})\n"
                     f"similarity dim ≈ {d:.3f}", fontsize=10)
        ax.set_aspect("equal")
        ax.axis("off")
    fig.suptitle(
        "K4 breadth: the de Rham w-family — many shapes from one parameter "
        "(fractal dimension = the non-∅-axiom edge)",
        fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "shapes sweep continuously in one complex w; the SL(2,ℤ)-generator "
             "half of K4 (metallic tower, golden = disc d) is ∅-axiom in "
             "Px/MetallicGeneratorTower.lean.",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.05, 1, 0.94])
    out = "research-notes/geometric/derham_family.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
