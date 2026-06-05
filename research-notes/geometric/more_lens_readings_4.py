"""More Lens readings of the slash — fourth batch (limits + intermediate stages).

  A. IFS of affine maps    Barnsley fern — the slash read as a *system* of
     contractions (the chaos game); limit a biological attractor.
  B. Newton step           z ↦ z − p/p' for z³−1 — the relation read as
     root-finding; limit the basins of the three roots (a fractal boundary).
  C. 2-D removal           Sierpinski carpet (dim log8/log3 ≈ 1.893) — the 2-D
     companion of the mod / XOR Sierpinski family.
  D. branching square      Pythagoras tree — the relation read as binary
     branching; self-similar canopy.
  E. cubic recurrence      plastic number ρ ≈ 1.3247  (x³ = x+1) — φ's *cubic*
     sibling, the next minimal Pisot number; the Padovan/Perrin spiral.
  F. three-fold inflation  Koch snowflake (dim log4/log3 ≈ 1.262) — the closed
     de Rham member; the relation = insert a bump.

Tier-1 exploratory.  Run:  python3 research-notes/geometric/more_lens_readings_4.py
"""

import numpy as np
import matplotlib.pyplot as plt


# ---- A. Barnsley fern (IFS chaos game) --------------------------------------
def panel_fern(ax, N=80000):
    rng = np.random.default_rng(0)
    x, y = 0.0, 0.0
    xs = np.empty(N); ys = np.empty(N)
    for i in range(N):
        r = rng.random()
        if r < 0.01:
            x, y = 0.0, 0.16 * y
        elif r < 0.86:
            x, y = 0.85 * x + 0.04 * y, -0.04 * x + 0.85 * y + 1.6
        elif r < 0.93:
            x, y = 0.20 * x - 0.26 * y, 0.23 * x + 0.22 * y + 1.6
        else:
            x, y = -0.15 * x + 0.28 * y, 0.26 * x + 0.24 * y + 0.44
        xs[i], ys[i] = x, y
    ax.scatter(xs, ys, s=0.15, color="#2a9d6f")
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title("A. slash = IFS of affine maps → Barnsley fern\n"
                 "the relation read as a system of contractions", fontsize=10)


# ---- B. Newton fractal z³−1 -------------------------------------------------
def panel_newton(ax, res=600, it=40):
    x = np.linspace(-1.5, 1.5, res); y = np.linspace(-1.5, 1.5, res)
    X, Y = np.meshgrid(x, y); Z = X + 1j * Y
    roots = np.exp(2j * np.pi * np.arange(3) / 3)
    for _ in range(it):
        Z = Z - (Z ** 3 - 1) / (3 * Z ** 2 + 1e-12)
    idx = np.argmin(np.abs(Z[..., None] - roots[None, None, :]), axis=2)
    ax.imshow(idx, cmap="viridis", origin="lower", extent=[-1.5, 1.5, -1.5, 1.5])
    ax.set_title("B. slash = Newton step  z↦z−p/p'  (z³−1)\n"
                 "basins of the three roots; fractal boundary", fontsize=10)
    ax.set_xticks([]); ax.set_yticks([])


# ---- C. Sierpinski carpet ---------------------------------------------------
def panel_carpet(ax, k=5):
    N = 3 ** k

    def keep(i, j):
        for _ in range(k):
            if i % 3 == 1 and j % 3 == 1:
                return 0
            i //= 3; j //= 3
        return 1
    M = np.fromfunction(np.vectorize(keep), (N, N), dtype=int)
    ax.imshow(M, cmap="magma", origin="lower", interpolation="nearest")
    ax.set_title("C. slash = 2-D removal → Sierpinski carpet\n"
                 "dim log8/log3 ≈ 1.893 (the 2-D mod/XOR companion)", fontsize=10)
    ax.set_xticks([]); ax.set_yticks([])


# ---- D. Pythagoras tree -----------------------------------------------------
def panel_pythagoras(ax, maxd=9):
    cmap = plt.get_cmap("viridis")

    def rec(p1, p2, depth):
        if depth > maxd:
            return
        d = p2 - p1
        p4 = p1 + d * 1j; p3 = p2 + d * 1j
        sq = np.array([p1, p2, p3, p4, p1])
        ax.fill(sq.real, sq.imag, color=cmap(depth / maxd), lw=0)
        apex = (p3 + p4) / 2 + ((p3 - p4) / 2) * 1j
        rec(p4, apex, depth + 1)
        rec(apex, p3, depth + 1)

    rec(-0.5 + 0j, 0.5 + 0j, 0)
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title("D. slash = branching square → Pythagoras tree\n"
                 "the relation read as binary branching", fontsize=10)


# ---- E. plastic number / Padovan spiral -------------------------------------
def panel_plastic(ax):
    # rho = real root of x^3 = x + 1 (the plastic number), phi's cubic sibling
    rho = np.cbrt(0.5 + np.sqrt(23 / 108)) + np.cbrt(0.5 - np.sqrt(23 / 108))
    theta = np.linspace(0, 7 * np.pi, 1500)
    r = rho ** (theta / (2 * np.pi / 3))   # grows by rho every 120°
    ax.plot(r * np.cos(theta), r * np.sin(theta), color="#d1495b", lw=1.6)
    ax.scatter([0], [0], s=20, color="0.2")
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title("E. slash = cubic recurrence  x³ = x+1\n"
                 f"plastic number ρ ≈ {rho:.4f} (φ's cubic sibling); Padovan spiral",
                 fontsize=10)


# ---- F. Koch snowflake ------------------------------------------------------
def panel_koch(ax, order=5):
    def koch(p1, p2, d):
        if d == 0:
            return [p1]
        a = p1 + (p2 - p1) / 3
        b = p1 + 2 * (p2 - p1) / 3
        peak = a + (b - a) * np.exp(-1j * np.pi / 3)
        return (koch(p1, a, d - 1) + koch(a, peak, d - 1)
                + koch(peak, b, d - 1) + koch(b, p2, d - 1))
    verts = [np.exp(1j * (np.pi / 2 + k * 2 * np.pi / 3)) for k in range(3)]
    pts = []
    for k in range(3):
        pts += koch(verts[k], verts[(k + 1) % 3], order)
    pts.append(pts[0])
    pts = np.array(pts)
    ax.fill(pts.real, pts.imag, color="#3b6fb0", alpha=0.25)
    ax.plot(pts.real, pts.imag, color="#3b6fb0", lw=0.6)
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title("F. slash = three-fold inflation → Koch snowflake\n"
                 "dim log4/log3 ≈ 1.262 (the closed de Rham member)", fontsize=10)


def main():
    fig, axes = plt.subplots(2, 3, figsize=(17, 10))
    fig.patch.set_facecolor("white")
    panel_fern(axes[0, 0])
    panel_newton(axes[0, 1])
    panel_carpet(axes[0, 2])
    panel_pythagoras(axes[1, 0])
    panel_plastic(axes[1, 1])
    panel_koch(axes[1, 2])
    fig.suptitle("More Lens readings of the slash — batch 4 "
                 "(IFS / root-basins / 2-D removal / branching / cubic Pisot / Koch)",
                 fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.95])
    out = "research-notes/geometric/more_lens_readings_4.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
