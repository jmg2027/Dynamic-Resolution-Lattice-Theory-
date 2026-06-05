"""More Lens readings of the slash — second batch (limits + intermediate stages).

Six further combining maps, each a Lens with its own limit and characteristic
intermediate stage:

  A. mediant ↔ midpoint glued   Minkowski ?(x)  — the singular self-similar map
     sending the Stern–Brocot order to the dyadic order; ties the whole atlas
     (mediant reading vs betweenness reading) into one function.
  B. pairing                    Hilbert curve   — the slash read as a pairing of
     two coordinates; limit a space-filling curve (dim 2).
  C. Pascal mod p               mod-3 Sierpinski (dim log6/log3 ≈ 1.631) — XOR
     (p=2) is one member of a prime-indexed family of discrete fractals.
  D. golden substitution        Fibonacci word / cut-and-project — aperiodic
     order; φ as a quasicrystal (the same φ of §3.5, a third frame).
  E. mediant on ℍ               Farey / modular tessellation — the mediant acting
     on the hyperbolic plane gives the ideal-triangle Farey tessellation.
  F. complex squaring  z↦z²+c   Julia set — the relation read as a complex map.

Tier-1 exploratory.  Run:  python3 research-notes/geometric/more_lens_readings_2.py
"""

import numpy as np
import matplotlib.pyplot as plt


# ---- A. Minkowski question-mark ---------------------------------------------
def question_mark(x, depth=40):
    a, y = [], x
    for _ in range(depth):
        if y <= 1e-12:
            break
        y = 1.0 / y
        ai = int(np.floor(y))
        a.append(ai)
        y -= ai
    s, acc, sign = 0.0, 0, 1
    for ai in a:
        acc += ai
        s += sign * 2.0 ** (-acc)
        sign = -sign
    return 2 * s


def panel_minkowski(ax):
    xs = np.linspace(0, 1, 2000)
    ax.plot(xs, [question_mark(x) for x in xs], color="#3b6fb0", lw=1.2)
    ax.plot([0, 1], [0, 1], color="0.7", ls=":", lw=1)
    ax.set_title("A. slash = mediant ↔ midpoint glued: Minkowski ?(x)\n"
                 "singular, self-similar — Stern–Brocot order → dyadic order",
                 fontsize=10)
    ax.set_aspect("equal"); ax.set_xlim(0, 1); ax.set_ylim(0, 1)
    ax.set_xticks([0, 0.5, 1]); ax.set_yticks([0, 0.5, 1])


# ---- B. Hilbert space-filling curve -----------------------------------------
def hilbert_xy(n, d):
    x = y = 0; t = d; s = 1
    while s < n:
        rx = 1 & (t // 2)
        ry = 1 & (t ^ rx)
        if ry == 0:
            if rx == 1:
                x = s - 1 - x; y = s - 1 - y
            x, y = y, x
        x += s * rx; y += s * ry
        t //= 4; s *= 2
    return x, y


def panel_hilbert(ax, order=6):
    n = 2 ** order
    pts = np.array([hilbert_xy(n, d) for d in range(n * n)])
    seg = np.linspace(0, 1, len(pts))
    ax.scatter(pts[:, 0], pts[:, 1], c=seg, cmap="viridis", s=1)
    ax.plot(pts[:, 0], pts[:, 1], color="0.6", lw=0.2, alpha=0.5)
    ax.set_title("B. slash = pairing → Hilbert curve\n"
                 "limit fills the square (dim 2); intermediate = order-n",
                 fontsize=10)
    ax.set_aspect("equal"); ax.axis("off")


# ---- C. Pascal mod p -> generalized Sierpinski ------------------------------
def panel_pascal_modp(ax, p=3, rows=81):
    M = np.zeros((rows, rows), dtype=int)
    M[0, 0] = 1
    for i in range(1, rows):
        M[i, 0] = 1
        for j in range(1, i + 1):
            M[i, j] = (M[i - 1, j - 1] + M[i - 1, j]) % p
    masked = np.ma.masked_where(np.triu(np.ones_like(M), 1).astype(bool), M)
    ax.imshow(masked, cmap="magma", origin="upper", interpolation="nearest")
    ax.set_title(f"C. slash = Pascal mod {p}  (XOR = p2 generalized)\n"
                 f"mod-{p} Sierpinski, dim log6/log3 ≈ 1.631",
                 fontsize=10)
    ax.set_xticks([]); ax.set_yticks([])


# ---- D. golden substitution -> Fibonacci cut-and-project --------------------
def panel_fibonacci(ax, N=60):
    phi = (1 + np.sqrt(5)) / 2
    slope = 1.0 / phi
    # lattice points just below the golden line, projected -> Fibonacci tiling
    xs, ys, cols = [], [], []
    j = 0
    for i in range(N):
        # the staircase: step right (long, L) or up (short, S)
        pass
    # build the staircase explicitly
    x, y = 0, 0
    path = [(0, 0)]
    for _ in range(N):
        # next lattice step keeping closest below line y = slope*x  (Christoffel)
        if (y + 1) <= slope * (x + 0.5):
            y += 1
        else:
            x += 1
        path.append((x, y))
    path = np.array(path)
    ax.plot(path[:, 0], path[:, 1], "-o", ms=2, color="#7a3bb0", lw=1)
    xx = np.linspace(0, path[:, 0].max(), 50)
    ax.plot(xx, slope * xx, color="#d1495b", lw=1, ls="--", label="slope 1/φ")
    ax.set_title("D. slash = golden substitution → Fibonacci word\n"
                 "cut-and-project staircase; φ as aperiodic order",
                 fontsize=10)
    ax.set_aspect("equal"); ax.legend(fontsize=8, loc="upper left")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


# ---- E. Farey / modular tessellation in the hyperbolic upper half-plane -----
def farey(n):
    a, b, c, d = 0, 1, 1, n
    seq = [(0, 1)]
    while c <= n:
        k = (n + b) // d
        a, b, c, d = c, d, k * c - a, k * d - b
        seq.append((a, b))
    return seq


def panel_farey(ax, depth=6):
    # Stern–Brocot recursion: every mediant-neighbour pair is an ideal-triangle
    # edge (a geodesic semicircle), nested across levels.
    arcs = []

    def rec(lo, hi, d):
        arcs.append((lo, hi))
        if d == 0:
            return
        med = (lo[0] + hi[0], lo[1] + hi[1])
        rec(lo, med, d - 1)
        rec(med, hi, d - 1)

    rec((0, 1), (1, 1), depth)
    th = np.linspace(0, np.pi, 100)
    cmap = plt.get_cmap("viridis")
    for (a, b), (c, d) in arcs:
        x0, x1 = a / b, c / d
        cx, r = (x0 + x1) / 2, abs(x1 - x0) / 2
        ax.plot(cx + r * np.cos(th), r * np.sin(th),
                color=cmap(min(1.0, 1 - r)), lw=0.9)
    ax.plot([0, 0], [0, 0.62], color="0.6", lw=1)
    ax.plot([1, 1], [0, 0.62], color="0.6", lw=1)
    ax.set_title("E. slash = mediant on ℍ → Farey tessellation\n"
                 "ideal-triangle (modular) tiling; neighbours ⟺ |ps−qr|=1",
                 fontsize=10)
    ax.set_xlim(-0.05, 1.05); ax.set_ylim(0, 0.62)
    ax.set_xticks([0, 0.5, 1]); ax.set_yticks([])


# ---- F. complex squaring -> Julia set ---------------------------------------
def panel_julia(ax, c=-0.123 + 0.745j, res=600, it=60):
    x = np.linspace(-1.6, 1.6, res)
    y = np.linspace(-1.6, 1.6, res)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    esc = np.zeros(Z.shape)
    for k in range(it):
        m = np.abs(Z) < 4
        Z[m] = Z[m] ** 2 + c
        esc[m & (np.abs(Z) >= 4)] = k
    esc[esc == 0] = it
    ax.imshow(esc, cmap="magma", origin="lower", extent=[-1.6, 1.6, -1.6, 1.6])
    ax.set_title("F. slash = complex squaring  z ↦ z²+c\n"
                 "Julia set (Douady rabbit, c=−0.123+0.745i)",
                 fontsize=10)
    ax.set_xticks([]); ax.set_yticks([])


def main():
    fig, axes = plt.subplots(2, 3, figsize=(17, 10))
    fig.patch.set_facecolor("white")
    panel_minkowski(axes[0, 0])
    panel_hilbert(axes[0, 1])
    panel_pascal_modp(axes[0, 2])
    panel_fibonacci(axes[1, 0])
    panel_farey(axes[1, 1])
    panel_julia(axes[1, 2])
    fig.suptitle("More Lens readings of the slash — batch 2 "
                 "(singular function / space-filling / mod-p / aperiodic / hyperbolic / complex)",
                 fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.95])
    out = "research-notes/geometric/more_lens_readings_2.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
