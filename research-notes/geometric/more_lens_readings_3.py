"""More Lens readings of the slash — third batch (limits + intermediate stages).

  A. tangent-circle relation   Apollonian gasket — the relation of two (three)
     mutually tangent circles IS a new tangent circle (Descartes); the most
     literal "relation of two → a third" reading; limit dim ≈ 1.3057.
  B. tunable nonlinear map      logistic x↦r·x(1−x), sweep r — a *constant pops
     out*: the Feigenbaum δ ≈ 4.669 governs the period-doubling cascade, the way
     φ governs the mediant reading.
  C. five-fold inflation        pentaflake — φ in a 2-D aperiodic/self-similar
     reading (a fourth φ-frame); dim log6/log(2+φ).
  D. paper-folding              Heighway dragon — an L-system reading; limit tiles
     the plane (dim 2).
  E. Calkin–Wilf recurrence     the *other* enumeration of ℚ (a/(a+b), (a+b)/b) —
     every rational once, a sibling of the Stern–Brocot/mediant reading.
  F. random midpoint            fractional Brownian motion — the *stochastic*
     reading of betweenness: midpoint + noise, a different KIND of Lens.

Tier-1 exploratory.  Run:  python3 research-notes/geometric/more_lens_readings_3.py
"""

import numpy as np
import matplotlib.pyplot as plt
import cmath, math


# ---- A. Apollonian gasket ----------------------------------------------------
def panel_apollonian(ax, depth=8):
    def fourth(c1, c2, c3, sign):
        (k1, z1), (k2, z2), (k3, z3) = c1, c2, c3
        k4 = k1 + k2 + k3 + sign * 2 * math.sqrt(abs(k1 * k2 + k2 * k3 + k3 * k1))
        zk = (k1 * z1 + k2 * z2 + k3 * z3
              + sign * 2 * cmath.sqrt(k1 * k2 * z1 * z2 + k2 * k3 * z2 * z3
                                      + k1 * k3 * z1 * z3))
        return (k4, zk / k4)

    def companion(t1, t2, t3, ex):
        # Descartes reflection: the two solutions sum to 2·(sum of three); no sqrt
        k = 2 * (t1[0] + t2[0] + t3[0]) - ex[0]
        bz = (2 * (t1[0] * t1[1] + t2[0] * t2[1] + t3[0] * t3[1]) - ex[0] * ex[1])
        return (k, bz / k)

    circles = {}

    def add(c):
        k, z = c
        key = (round(k, 3), round(z.real, 3), round(z.imag, 3))
        if key not in circles and abs(k) < 6000:
            circles[key] = c
            return True
        return False

    outer = (-1.0, 0 + 0j)
    c2 = (2.0, -0.5 + 0j)
    c3 = (2.0, 0.5 + 0j)
    c4 = fourth(outer, c2, c3, +1)
    c4m = fourth(outer, c2, c3, -1)
    for c in (outer, c2, c3, c4, c4m):
        add(c)

    def go(c1, c2_, c3_, c4_, d):
        if d == 0:
            return
        for a, b, c, ex in ((c1, c2_, c3_, c4_), (c1, c2_, c4_, c3_),
                            (c1, c3_, c4_, c2_), (c2_, c3_, c4_, c1)):
            nw = companion(a, b, c, ex)
            if add(nw):
                go(a, b, c, nw, d - 1)

    go(outer, c2, c3, c4, depth)
    go(outer, c2, c3, c4m, depth)

    th = np.linspace(0, 2 * np.pi, 60)
    cmap = plt.get_cmap("viridis")
    for k, z in circles.values():
        r = abs(1.0 / k)
        col = "0.3" if k < 0 else cmap(min(1.0, math.log(abs(k) + 1) / 7))
        ax.plot(z.real + r * np.cos(th), z.imag + r * np.sin(th), color=col, lw=0.5)
    ax.set_aspect("equal"); ax.set_xlim(-1.05, 1.05); ax.set_ylim(-1.05, 1.05)
    ax.axis("off")
    ax.set_title("A. slash = relation of tangent circles (Descartes)\n"
                 "Apollonian gasket, dim ≈ 1.3057", fontsize=10)


# ---- B. logistic bifurcation -> Feigenbaum ----------------------------------
def panel_logistic(ax):
    rs = np.linspace(2.5, 4.0, 1200)
    for r in rs:
        x = 0.5
        for _ in range(300):
            x = r * x * (1 - x)
        pts = []
        for _ in range(120):
            x = r * x * (1 - x)
            pts.append(x)
        ax.plot([r] * len(pts), pts, ",", color="#3b6fb0", alpha=0.25)
    ax.set_title("B. slash = tunable map  x↦r·x(1−x)\n"
                 "period-doubling → chaos; the constant δ ≈ 4.669 (Feigenbaum)",
                 fontsize=10)
    ax.set_xlabel("r", fontsize=8); ax.set_ylabel("attractor x", fontsize=8)
    ax.set_xlim(2.5, 4.0); ax.set_ylim(0, 1)


# ---- C. pentaflake ----------------------------------------------------------
def panel_pentaflake(ax, depth=4):
    phi = (1 + np.sqrt(5)) / 2
    ratio = 1.0 / (1 + phi)
    ang = np.pi / 2 + np.arange(5) * 2 * np.pi / 5

    def draw(cx, cy, R, d):
        if d == 0:
            px = cx + R * np.cos(ang); py = cy + R * np.sin(ang)
            ax.fill(px, py, color="#7a3bb0", lw=0)
            return
        r = R * ratio
        for a in ang:
            draw(cx + (R - r) * np.cos(a), cy + (R - r) * np.sin(a), r, d - 1)
        draw(cx, cy, r, d - 1)

    draw(0, 0, 1, depth)
    ax.set_aspect("equal"); ax.set_xlim(-1.1, 1.1); ax.set_ylim(-1.1, 1.1)
    ax.axis("off")
    ax.set_title("C. slash = five-fold inflation → pentaflake\n"
                 "φ in a 2-D self-similar reading (5-fold)", fontsize=10)


# ---- D. Heighway dragon -----------------------------------------------------
def panel_dragon(ax, order=12):
    turns = []
    for _ in range(order):
        turns = turns + [1] + [-t for t in reversed(turns)]
    x, y, hd = 0.0, 0.0, 0.0
    pts = [(x, y)]
    for t in turns + [1]:
        x += np.cos(hd); y += np.sin(hd)
        pts.append((x, y))
        hd += t * np.pi / 2
    pts = np.array(pts)
    seg = np.linspace(0, 1, len(pts))
    ax.scatter(pts[:, 0], pts[:, 1], c=seg, cmap="magma", s=1)
    ax.plot(pts[:, 0], pts[:, 1], color="0.6", lw=0.2, alpha=0.4)
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title("D. slash = paper-folding → Heighway dragon\n"
                 "L-system; limit tiles the plane (dim 2)", fontsize=10)


# ---- E. Calkin-Wilf tree ----------------------------------------------------
def panel_calkin_wilf(ax, depth=5):
    # node (a,b) -> children (a, a+b) and (a+b, b)
    levels = [[(1, 1)]]
    for _ in range(depth):
        nxt = []
        for (a, b) in levels[-1]:
            nxt.append((a, a + b)); nxt.append((a + b, b))
        levels.append(nxt)
    cmap = plt.get_cmap("viridis")
    pos = {}
    for d, lvl in enumerate(levels):
        n = len(lvl)
        for i, frac in enumerate(lvl):
            x = (i + 0.5) / n
            pos[(d, i)] = (x, -d)
            ax.scatter([x], [-d], s=90, color=cmap(d / depth),
                       edgecolors="white", linewidths=0.8, zorder=3)
            if d <= 3:
                ax.text(x, -d + 0.22, f"{frac[0]}/{frac[1]}", ha="center",
                        fontsize=6.5, color="0.25")
    for d in range(depth):
        for i in range(len(levels[d])):
            for ci in (2 * i, 2 * i + 1):
                x0, y0 = pos[(d, i)]; x1, y1 = pos[(d + 1, ci)]
                ax.plot([x0, x1], [y0, y1], color="0.6", lw=0.6, alpha=0.5, zorder=1)
    ax.set_title("E. slash = Calkin–Wilf recurrence\n"
                 "the other enumeration of ℚ (each rational once)", fontsize=10)
    ax.axis("off")


# ---- F. fractional Brownian (random midpoint displacement) ------------------
def panel_fbm(ax, depth=11, H=0.7, seed=7):
    rng = np.random.default_rng(seed)
    n = 2 ** depth
    h = np.zeros(n + 1)
    step = n
    scale = 1.0
    while step > 1:
        half = step // 2
        for i in range(half, n + 1, step):
            h[i] = 0.5 * (h[i - half] + h[i + half]) + rng.normal(0, scale)
        scale *= 0.5 ** H
        step = half
    xs = np.linspace(0, 1, n + 1)
    ax.plot(xs, h, color="#2a9d6f", lw=0.8)
    ax.fill_between(xs, h, h.min() - 0.2, color="#2a9d6f", alpha=0.15)
    ax.set_title("F. slash = random midpoint (stochastic between)\n"
                 "fractional Brownian motion; the random reading", fontsize=10)
    ax.set_xlim(0, 1); ax.axis("off")


def main():
    fig, axes = plt.subplots(2, 3, figsize=(17, 10))
    fig.patch.set_facecolor("white")
    panel_apollonian(axes[0, 0])
    panel_logistic(axes[0, 1])
    panel_pentaflake(axes[0, 2])
    panel_dragon(axes[1, 0])
    panel_calkin_wilf(axes[1, 1])
    panel_fbm(axes[1, 2])
    fig.suptitle("More Lens readings of the slash — batch 3 "
                 "(circle-packing / chaos / aperiodic / L-system / rational tree / stochastic)",
                 fontsize=14, fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.95])
    out = "research-notes/geometric/more_lens_readings_3.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
