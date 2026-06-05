"""More Lens readings of the slash — a shape catalog (limits + intermediate stages).

The slash ("the relation of two objects is an object, recurse") supports many
readings beyond betweenness / free / mediant / de Rham.  Each combining map is a
Lens; each gives a characteristic limit and a characteristic intermediate stage.
Six further readings, drawn:

  A. power-mean between   M_p(x,y) = ((x^p+y^p)/2)^{1/p}  — the "between" is a
     one-parameter family (harmonic/geometric/arithmetic/…); all fill [a,b],
     skewed by p; arithmetic (p=1) is the symmetric one.
  B. XOR / Nim            x ⊕ y (bitwise)  — limit the Sierpinski gasket
     (dim log3/log2 ≈ 1.585); intermediate the n-bit table (Pascal mod 2).
  C. mediant / Ford       (p+r)/(q+s)  — tangency ⟺ mediant neighbours; limit
     the Ford circle packing over all rationals.
  D. modular              (x+y) mod n  — a finite / periodic limit: the n-gon
     (ℤ_n), tending to the circle as n grows.
  E. golden rotation      rotate by the golden angle  — equidistribution
     (the sunflower); φ is the most uniform rotation (ties to §3.5 φ).
  F. concatenation        word x·y (§6.4 syntactic internalisation)  — limit the
     Cantor set (dim log2/log3 ≈ 0.631); intermediate 2^n intervals.

These are tier-1 exploratory readings; a reading promotes only when a discrete
cell closes ∅-axiom.  Run:  python3 research-notes/geometric/more_lens_readings.py
"""

import numpy as np
import matplotlib.pyplot as plt
from math import gcd, log


# ---- A. power-mean between family -------------------------------------------
def power_mean(a, b, p):
    if abs(p) < 1e-9:
        return np.sqrt(a * b)
    return ((a ** p + b ** p) / 2) ** (1.0 / p)


def panel_power_mean(ax):
    a, b = 1.0, 4.0
    ps = np.linspace(-8, 8, 400)
    vals = [power_mean(a, b, p) for p in ps]
    ax.plot(ps, vals, color="#3b6fb0", lw=2)
    for p0, name in [(-1, "harmonic"), (0, "geometric"), (1, "arithmetic"),
                     (2, "quadratic")]:
        v = power_mean(a, b, p0)
        ax.scatter([p0], [v], s=40, color="#d1495b", zorder=5)
        ax.annotate(f"{name}\n{v:.2f}", (p0, v), textcoords="offset points",
                    xytext=(6, -2), fontsize=7.5, color="0.3")
    ax.axhline(a, color="0.6", ls=":", lw=1); ax.axhline(b, color="0.6", ls=":", lw=1)
    ax.text(8, a + 0.05, "min", fontsize=8, color="0.5", ha="right")
    ax.text(8, b - 0.2, "max", fontsize=8, color="0.5", ha="right")
    ax.set_title("A. slash = power-mean between M_p\n"
                 "the 'between' is a 1-param family; limit = warped segment",
                 fontsize=10)
    ax.set_xlabel("p", fontsize=8); ax.set_ylabel("M_p(1,4)", fontsize=8)


# ---- B. XOR / Nim -> Sierpinski ---------------------------------------------
def panel_sierpinski(ax, n=7):
    N = 2 ** n
    M = np.fromfunction(lambda i, j: ((i.astype(int) & j.astype(int)) == 0),
                        (N, N))
    ax.imshow(M, cmap="magma", origin="lower", interpolation="nearest")
    ax.set_title("B. slash = XOR / Nim  (x ⊕ y)\n"
                 f"limit = Sierpinski, dim log3/log2 ≈ 1.585; intermediate = {n}-bit",
                 fontsize=10)
    ax.set_xticks([]); ax.set_yticks([])


# ---- C. mediant -> Ford circles ---------------------------------------------
def panel_ford(ax, Q=14):
    cmap = plt.get_cmap("viridis")
    for q in range(1, Q + 1):
        for p in range(0, q + 1):
            if gcd(p, q) == 1:
                r = 1.0 / (2 * q * q)
                ax.add_patch(plt.Circle((p / q, r), r, color=cmap(1 - q / Q),
                                        alpha=0.7, lw=0))
    ax.set_xlim(-0.02, 1.02); ax.set_ylim(0, 0.58)
    ax.set_aspect("equal")
    ax.set_title("C. slash = mediant  (p+r)/(q+s)\n"
                 "tangency ⟺ mediant neighbours; limit = Ford packing (all ℚ)",
                 fontsize=10)
    ax.set_xticks([0, 0.5, 1]); ax.set_yticks([])


# ---- D. modular -> n-gon -> circle ------------------------------------------
def panel_modular(ax):
    th = np.linspace(0, 2 * np.pi, 400)
    ax.plot(np.cos(th), np.sin(th), color="0.85", lw=1)
    cmap = plt.get_cmap("plasma")
    for k, n in enumerate([3, 6, 12, 24]):
        a = np.linspace(0, 2 * np.pi, n + 1)
        ax.plot(np.cos(a), np.sin(a), "-o", ms=3, lw=1.3,
                color=cmap(k / 3), label=f"n={n}")
    ax.set_aspect("equal"); ax.axis("off")
    ax.legend(fontsize=7, loc="center")
    ax.set_title("D. slash = (x+y) mod n\n"
                 "finite / periodic limit: the n-gon (ℤ_n) → circle as n grows",
                 fontsize=10)


# ---- E. golden rotation -> equidistribution (sunflower) ---------------------
def panel_golden(ax, N=700):
    phi = (1 + np.sqrt(5)) / 2
    k = np.arange(1, N + 1)
    theta = 2 * np.pi * k / phi ** 2
    r = np.sqrt(k)
    ax.scatter(r * np.cos(theta), r * np.sin(theta), c=k, cmap="viridis", s=6)
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title("E. slash = rotate by the golden angle\n"
                 "equidistribution (sunflower); φ = the most uniform rotation",
                 fontsize=10)


# ---- F. concatenation -> Cantor set -----------------------------------------
def panel_cantor(ax, depth=6):
    def cantor(intervals):
        out = []
        for x0, x1 in intervals:
            t = (x1 - x0) / 3.0
            out.append((x0, x0 + t)); out.append((x1 - t, x1))
        return out
    intervals = [(0.0, 1.0)]
    for d in range(depth + 1):
        for x0, x1 in intervals:
            ax.plot([x0, x1], [-d, -d], color="#7a3bb0", lw=3, solid_capstyle="butt")
        intervals = cantor(intervals)
    ax.set_ylim(-depth - 0.6, 0.6); ax.set_xlim(-0.03, 1.03)
    ax.axis("off")
    ax.set_title("F. slash = concatenate (§6.4 syntactic)\n"
                 "limit = Cantor set, dim log2/log3 ≈ 0.631; intermediate = 2^n intervals",
                 fontsize=10)


def main():
    fig, axes = plt.subplots(2, 3, figsize=(17, 10))
    fig.patch.set_facecolor("white")
    panel_power_mean(axes[0, 0])
    panel_sierpinski(axes[0, 1])
    panel_ford(axes[0, 2])
    panel_modular(axes[1, 0])
    panel_golden(axes[1, 1])
    panel_cantor(axes[1, 2])
    fig.suptitle("More Lens readings of the slash — a shape catalog "
                 "(each combining map = a Lens; each its own limit + intermediate)",
                 fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.95])
    out = "research-notes/geometric/more_lens_readings.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
