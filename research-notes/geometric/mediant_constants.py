"""Where 3, 2, 5, the Mobius matrix and phi pop out of "object = relation of two".

The earlier geometric renderings used maximally-symmetric embeddings -- the
arithmetic midpoint (a+b)/2 and the regular simplex -- which quotient away the
asymmetry the structural constants live in.  Continuous geometry is blind to
them (CLAUDE.md algebraic-priority: DRLT constants come from counting, not
continuous variation).

The constants are the *algebraic form* of the slash.  Per 03_form.md 3.5, the
four clauses written algebraically ARE the Mobius matrix

        P = [[2,1],[1,1]],   P(x) = (2x+1)/(x+1)
        trace 3 = NS,  det 1 = the glue (NS-NT=1),  disc 9-4 = 5 = NS+NT,
        eigenvalues (3 +- sqrt5)/2 = phi^2, 1/phi^2.

P is the Fibonacci matrix squared:  [[1,1],[1,0]]^2 = [[2,1],[1,1]].  The "between"
that carries P is not the midpoint but the MEDIANT (Stern-Brocot):

        p/q  *  r/s   =   (p+r)/(q+s)

-- a genuinely new, prim-distinct rational each time (no collapse, unlike the
midpoint; no over-symmetrization, unlike the regular simplex).  Iterating the
mediant from the two seed atoms generates every rational once (Stern-Brocot),
det = 1 throughout (the off-diagonal glue), and the always-mediant spine runs
Fibonacci -> phi.  So the same construction yields 3, 2, 5, P, phi once the
relation is read algebraically.  K_{3,2}^{(c=2)} reads (NS,NT,d,c)=(3,2,5,2)
off the same P.

Run:  python3 research-notes/geometric/mediant_constants.py
"""

import numpy as np
import matplotlib.pyplot as plt


# ----------------------------------------------------------------------------
# Stern-Brocot mediant tree on [0,1]:  seeds 0/1 and 1/1, between = mediant
# ----------------------------------------------------------------------------
def build_tree(depth):
    """Return nodes {(p,q): (value, gen)} and parents {(p,q): ((p,q),(p,q))}."""
    nodes = {(0, 1): (0.0, 0), (1, 1): (1.0, 0)}
    parents = {}

    def rec(lo, hi, g):
        if g > depth:
            return
        m = (lo[0] + hi[0], lo[1] + hi[1])
        if m not in nodes:
            nodes[m] = (m[0] / m[1], g)
            parents[m] = (lo, hi)
        rec(lo, m, g + 1)
        rec(m, hi, g + 1)

    rec((0, 1), (1, 1), 1)
    return nodes, parents


def fib_spine(depth):
    """Fibonacci fractions F_n/F_{n+1} in [0,1] -> 1/phi (the always-mediant spine)."""
    F = [1, 1]
    for _ in range(depth + 2):
        F.append(F[-1] + F[-2])
    return [(F[n], F[n + 1]) for n in range(1, depth + 1)]


def draw_tree(ax, depth=6):
    nodes, parents = build_tree(depth)
    spine = set(fib_spine(depth))
    cmap = plt.get_cmap("viridis")

    for m, (lo, hi) in parents.items():
        xv, g = nodes[m][0], nodes[m][1]
        on_spine = m in spine
        col = "#d1495b" if on_spine else cmap(g / depth)
        for p in (lo, hi):
            ax.plot([xv, nodes[p][0]], [-g, -nodes[p][1]], color=col,
                    lw=1.8 if on_spine else 0.8, alpha=0.9 if on_spine else 0.4,
                    zorder=2 if on_spine else 1)
    for (p, q), (xv, g) in nodes.items():
        on_spine = (p, q) in spine or (p, q) in ((0, 1), (1, 1))
        col = "#d1495b" if (p, q) in spine else ("0.15" if g == 0 else cmap(g / depth))
        ax.scatter([xv], [-g], s=240 if g == 0 else 150, color=col,
                   edgecolors="white", linewidths=1.0, zorder=3)
        if g <= 3 or (p, q) in spine:
            ax.text(xv, -g + 0.18, f"{p}/{q}", ha="center", fontsize=7.5,
                    color="#d1495b" if (p, q) in spine else "0.25", zorder=4)

    ax.text(0.5, 0.55, "between = MEDIANT  p/q * r/s = (p+r)/(q+s)   (not the midpoint)",
            ha="center", fontsize=9.5, color="0.2")
    ax.text(0.5, -depth - 0.75,
            "red = Fibonacci spine  1/2, 2/3, 3/5, 5/8, … → 1/φ   (always-mediant path)",
            ha="center", fontsize=9, color="#d1495b")
    ax.set_title("the faithful 'between': Stern–Brocot mediant tree\n"
                 "every rational once, prim-distinct (no collapse), det = 1 throughout",
                 fontsize=11)
    ax.set_xlim(-0.05, 1.05)
    ax.set_ylim(-depth - 1.1, 0.9)
    ax.axis("off")


# ----------------------------------------------------------------------------
# Panel 2 — the Mobius matrix P and its readouts: 3, 2, 5, phi
# ----------------------------------------------------------------------------
def draw_constants(ax, depth=14):
    phi = (1 + np.sqrt(5)) / 2
    F = [1, 1]
    for _ in range(depth + 2):
        F.append(F[-1] + F[-2])
    n = np.arange(1, depth + 1)
    ratio = np.array([F[k + 1] / F[k] for k in n])  # -> phi

    ax.axhline(phi, color="0.6", ls="--", lw=1)
    ax.plot(n, ratio, "o-", color="#d1495b", ms=4, lw=1.5,
            label=r"$F_{n+1}/F_n \to \varphi$  (mediant spine)")
    ax.text(n[-1], phi + 0.03, r"$\varphi = \frac{1+\sqrt{5}}{2}$", ha="right",
            fontsize=11, color="0.3")
    ax.set_xlabel("spine depth n", fontsize=9)
    ax.set_ylabel(r"consecutive ratio $\to \varphi$", fontsize=9)
    ax.set_ylim(1.3, 2.05)
    ax.legend(fontsize=9, loc="lower right")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)

    txt = (
        "P = [[2, 1],\n"
        "       [1, 1]]   =   [[1,1],[1,0]]²   (Fibonacci matrix squared)\n\n"
        "trace = 3 = N_S\n"
        "det   = 1   (the glue, N_S − N_T = 1)\n"
        "disc  = 3² − 4 = 5 = N_S + N_T = d\n"
        "eigenvalues = φ², 1/φ²\n\n"
        "K_{3,2}^(c=2):  (N_S, N_T, d, c) = (3, 2, 5, 2)\n"
        "                  — same P, read off"
    )
    ax.text(0.04, 0.96, txt, transform=ax.transAxes, va="top", fontsize=9.5,
            family="monospace",
            bbox=dict(boxstyle="round", fc="#fff6f7", ec="#d1495b", alpha=0.95))
    ax.set_title("the constants are P read out\n"
                 "3, 2, 5, φ are the slash's algebraic form (03_form.md §3.5)",
                 fontsize=11)


def main():
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))
    fig.patch.set_facecolor("white")
    draw_tree(axes[0])
    draw_constants(axes[1])
    fig.suptitle(
        "where 3, 2, 5, the Möbius matrix and φ come from: "
        "read the relation as the mediant, not the midpoint",
        fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "midpoint / regular simplex = maximally symmetric = blind to the constants. "
             "mediant = the slash's algebraic form P = [[2,1],[1,1]].",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.05, 1, 0.95])
    out = "research-notes/geometric/mediant_constants.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
