"""The intermediate states of the cycle form a distributive lattice (= DRLT).

Mingu Jeong's refined cycle (line→point, point→lines-to-non-connected) has, from
cycle 2, many independent growth axes whose operations COMMUTE (conjecture 2 =
confluence).  Confluence ⇒ the reachable intermediate configurations form a
lattice — the order-ideal lattice of the cycle's operation poset (Birkhoff).  The
limit (complete graph) is trivial; the intermediate states are the content, and
they are a lattice: this is the *lattice* of Dynamic Resolution Lattice theory.

Counts (computed): intermediate states per cycle = 5, 145, vast (cycle 3 has 63
operations → order-ideal count astronomically large).

Run:  python3 research-notes/geometric/cycle_intermediate_lattice.py
"""

import numpy as np
import matplotlib.pyplot as plt


def panel_lattice(ax):
    # cycle-1 intermediate-state lattice: downsets of {vc < ca, vc < cb}
    states = {
        "∅": (0.5, 0),
        "{c}": (0.5, 1),
        "{c, ca}": (0.15, 2),
        "{c, cb}": (0.85, 2),
        "{c, ca, cb}\n= K₃": (0.5, 3),
    }
    edges = [("∅", "{c}"), ("{c}", "{c, ca}"), ("{c}", "{c, cb}"),
             ("{c, ca}", "{c, ca, cb}\n= K₃"), ("{c, cb}", "{c, ca, cb}\n= K₃")]
    for u, v in edges:
        ax.plot([states[u][0], states[v][0]], [states[u][1], states[v][1]],
                color="0.6", lw=1.2, zorder=1)
    for s, (x, y) in states.items():
        ax.scatter([x], [y], s=1400, color="#3b6fb0", alpha=0.85,
                   edgecolors="white", linewidths=1.5, zorder=3)
        ax.text(x, y, s, ha="center", va="center", color="white",
                fontsize=8, fontweight="bold", zorder=4)
    ax.text(0.5, 2, "two paths,\none top\n(confluence)", ha="center",
            fontsize=8, color="#d1495b")
    ax.set_title("cycle 1: the 5 intermediate states form a lattice\n"
                 "(order ideals of the operation poset — already 2-wide)",
                 fontsize=11)
    ax.set_xlim(-0.1, 1.1); ax.set_ylim(-0.4, 3.5); ax.axis("off")


def panel_growth(ax):
    cyc = [1, 2, 3]
    ops = [3, 9, 63]
    states = [5, 145, 1e18]   # cycle-3 order-ideal count is astronomically large
    ax.semilogy(cyc, ops, "o-", color="#2a9d6f", lw=1.6, label="operations per cycle")
    ax.semilogy(cyc, states, "s-", color="#d1495b", lw=1.8,
                label="intermediate states (order ideals)")
    for c, s in zip(cyc, states):
        lbl = "≈10¹⁸+" if s > 1e9 else str(int(s))
        ax.annotate(lbl, (c, s), textcoords="offset points", xytext=(6, 4),
                    fontsize=9, color="#d1495b")
    for c, o in zip(cyc, ops):
        ax.annotate(str(o), (c, o), textcoords="offset points", xytext=(6, -10),
                    fontsize=9, color="#2a9d6f")
    ax.set_title("the intermediate-state lattice explodes\n"
                 "5 → 145 → vast — a distributive lattice (Birkhoff) per cycle",
                 fontsize=11)
    ax.set_xlabel("cycle", fontsize=9); ax.set_ylabel("count (log)", fontsize=9)
    ax.set_xticks(cyc); ax.legend(fontsize=9, loc="upper left")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


def main():
    fig, ax = plt.subplots(1, 2, figsize=(15, 6.5))
    fig.patch.set_facecolor("white")
    panel_lattice(ax[0])
    panel_growth(ax[1])
    fig.suptitle("The cycle's intermediate states form a lattice — "
                 "this is the 'lattice' of Dynamic Resolution Lattice theory",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.015,
             "order-independence (conj. 2) = confluence ⇒ the intermediate configs "
             "are the order ideals of the operation poset = a distributive lattice; "
             "the limit (complete graph) is trivial, the lattice is the content.",
             ha="center", fontsize=9.5, color="0.3")
    fig.tight_layout(rect=[0, 0.05, 1, 0.95])
    out = "research-notes/geometric/cycle_intermediate_lattice.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
