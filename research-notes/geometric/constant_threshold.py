"""Testing conjecture C1: where do the constants 3, 5, phi switch on?

The combining map "relation of two" is a Mobius iteration on a fraction-pair.
Generalize the slash's algebraic form P=[[2,1],[1,1]] (03_form.md 3.5) by one
knob a -- the top-left entry, which 3.5 reads as "two somethings" (the count-Lens
reading of the distinguishing) -- keeping the off-diagonal glue fixed at 1:

        M_a = [[a, 1],
               [1, 1]],     M_a(x) = (a x + 1)/(x + 1)

    det   = a - 1          (the glue: det = 1  <=>  a = 2)
    trace = a + 1
    disc  = (a+1)^2 - 4(a-1) = a^2 - 2a + 5
    fixed point  x*(a) = [ (a-1) + sqrt((a-1)^2 + 4) ] / 2

The knob a literally interpolates between the two ends of the atlas:

  a = 1  ->  det = 0, M_1(x) = (x+1)/(x+1) = 1 : RANK-1 COLLAPSE.  Every input is
             sent to one value -- the averaging / midpoint degenerate end, the
             "continuum that degenerates to a point".  Blind: no structure.
             (3.2: "could one something suffice? No" -- one-something distinguishing.)

  a = 2  ->  det = 1, x* = phi, trace = 3, disc = 5 : THE 213 CONSTANTS, exactly.
             And a = 2 is forced -- it is the count-Lens minimum of the first
             distinguishing ("two + binary", 3.2).  So the constants are not
             tuned: "two somethings" (a=2) and "the glue" (det=1) are the SAME
             point of this family, and that point is golden.

  a = 3  ->  det = 2, x* = 1 + sqrt(2) (silver ratio), disc = 8 : structured but
             not the minimal axiom point.  Integer a >= 2 give the metallic ratios.

Refined C1 (the test result): BLIND <=> det = 0 (the collapse, a=1, the
averaging/midpoint end).  Any det != 0 gives a quadratic-irrational fixed point
(structured, Mobius/continued-fraction).  The specific 213 values 3,5,phi sit at
a = 2 -- simultaneously the forced count ("two somethings", 3.2) and the
unimodular glue (det = 1, 3.5).  The earlier midpoint renderings were blind
because they were the a -> 1 collapse.

Run:  python3 research-notes/geometric/constant_threshold.py
"""

import numpy as np
import matplotlib.pyplot as plt


def fixed_point(a):
    return ((a - 1) + np.sqrt((a - 1) ** 2 + 4)) / 2


# ----------------------------------------------------------------------------
# Panel 1 — the invariants vs the knob a; the constants live only at a = 2
# ----------------------------------------------------------------------------
def draw_invariants(ax):
    a = np.linspace(1.0, 3.2, 400)
    phi = (1 + np.sqrt(5)) / 2

    ax.axvline(2, color="#d1495b", ls="--", lw=1.2, zorder=0)
    ax.axvline(1, color="0.6", ls=":", lw=1.2, zorder=0)
    ax.plot(a, a - 1, lw=1.8, color="#3b6fb0", label="det $= a-1$  (the glue)")
    ax.plot(a, a + 1, lw=1.8, color="#2a9d6f", label="trace $= a+1$")
    ax.plot(a, a ** 2 - 2 * a + 5, lw=1.8, color="#7a3bb0",
            label="disc $= a^2-2a+5$")
    ax.plot(a, fixed_point(a), lw=2.2, color="#d1495b",
            label="fixed point $x^*(a)$")

    # anchors
    pts = [
        (1, 0, "a=1: det 0\nCOLLAPSE (→ point)"),
        (2, 1, "det = 1"),
        (2, 3, "trace = 3 = N_S"),
        (2, 5, "disc = 5 = N_S+N_T"),
        (2, phi, "x* = φ"),
        (3, 1 + np.sqrt(2), "x* = 1+√2\n(silver, a=3)"),
    ]
    for xv, yv, txt in pts:
        ax.scatter([xv], [yv], s=42, color="0.1", zorder=5)
        ax.annotate(txt, (xv, yv), textcoords="offset points", xytext=(7, 4),
                    fontsize=7.5, color="0.25")

    ax.set_title("the constants are not tuned — they sit at a = 2\n"
                 '"two somethings" (§3.2) = the glue det=1 (§3.5) = golden',
                 fontsize=11)
    ax.set_xlabel("knob  a  =  top-left entry = count-Lens reading (how many somethings)",
                  fontsize=9)
    ax.set_ylabel("invariant value", fontsize=9)
    ax.legend(fontsize=8, loc="upper left")
    ax.set_ylim(-0.3, 8.5)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


# ----------------------------------------------------------------------------
# Panel 2 — the spine converges to x*(a): structure switches on leaving collapse
# ----------------------------------------------------------------------------
def draw_spines(ax):
    cmap = plt.get_cmap("viridis")
    avals = [1.0, 1.5, 2.0, 2.5, 3.0]
    N = 14
    phi = (1 + np.sqrt(5)) / 2
    for i, a in enumerate(avals):
        x = 1.0
        xs = [x]
        for _ in range(N):
            x = (a * x + 1) / (x + 1)
            xs.append(x)
        col = "#d1495b" if a == 2.0 else cmap(i / (len(avals) - 1))
        lw = 2.4 if a == 2.0 else 1.4
        lab = f"a={a}" + ("  → φ" if a == 2.0 else
                          ("  → 1 (collapse)" if a == 1.0 else ""))
        ax.plot(range(N + 1), xs, "o-", ms=3, lw=lw, color=col, label=lab)
    ax.axhline(phi, color="#d1495b", ls="--", lw=1)
    ax.text(N, phi + 0.04, "φ", color="#d1495b", fontsize=12, ha="right")
    ax.axhline(1.0, color="0.6", ls=":", lw=1)
    ax.text(N, 1.0 + 0.04, "1 (collapse)", color="0.5", fontsize=8, ha="right")

    ax.set_title("the always-combine spine  $x_{n+1}=(a x_n+1)/(x_n+1)$\n"
                 "structure switches on the moment you leave the collapse (a=1)",
                 fontsize=11)
    ax.set_xlabel("spine depth n", fontsize=9)
    ax.set_ylabel("spine value → $x^*(a)$", fontsize=9)
    ax.legend(fontsize=8, loc="center right")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


def main():
    fig, axes = plt.subplots(1, 2, figsize=(16, 6.5))
    fig.patch.set_facecolor("white")
    draw_invariants(axes[0])
    draw_spines(axes[1])
    fig.suptitle(
        "C1 test: blind ⟺ det = 0 (the averaging/midpoint collapse); "
        "3, 5, φ live exactly at a = 2 (two somethings = the glue)",
        fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "midpoint/averaging = the a→1, det→0 degenerate end (blind). "
             "mediant/Möbius P = a=2, det=1 (the 213 constants, forced by §3.2).",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.05, 1, 0.94])
    out = "research-notes/geometric/constant_threshold.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
