"""By what criterion are the free-graph's edges drawn?  The criterion is a Lens.

The slash `a/b` is a *symmetric ternary* incidence: one distinguishing event ties
`a`, `b`, and the residue `a/b` together (`a/b = b/a`, §3.3; operator = object,
§6.2).  Turning that into a binary graph requires CHOOSING which of the three
pairs become edges — and that choice is a sub-Lens, not given by the Raw.  The
earlier "free-graph" used one criterion (child → its two operands); it is not the
minimal one.  Four criteria on the SAME node set:

  A. parent-edges     a/b—a, a/b—b   (what the earlier analysis used): drops the
     a—b edge and imposes a child/parent (operator/object) direction §6.2 denies.
  B. 2-simplex        a—b, a—a/b, b—a/b: the full triangle of each slash event.
  C. operand-pairing  a—b only: connect the two distinguished, ignore the residue.
  D. hypergraph       each slash = one 3-vertex hyperedge {a,b,a/b}: NO reduction,
     NO direction — the minimal honest reading of the ternary incidence.

Same skeleton, four graphs: the adjacency criterion is itself a reading.

Run:  python3 research-notes/geometric/connection_criterion.py
"""

import numpy as np
import matplotlib.pyplot as plt

# the slash events: child = parent1 / parent2  (the ternary incidence {p1,p2,child})
events = {
    "c": ("a", "b"), "d": ("c", "a"), "e": ("c", "b"),
    "f": ("d", "a"), "g": ("d", "b"), "h": ("d", "c"), "i": ("d", "e"),
}
SEEDS = ["a", "b"]
order = SEEDS + list(events.keys())
gen = {"a": 0, "b": 0}
for ch, (x, y) in events.items():
    gen[ch] = max(gen[x], gen[y]) + 1
maxg = max(gen.values())

# one fixed neutral layout, shared by all panels
by_gen = {}
for o in order:
    by_gen.setdefault(gen[o], []).append(o)
pos = {}
for g, objs in by_gen.items():
    n = len(objs)
    xs = [0.0] if n == 1 else np.linspace(-1, 1, n)
    for o, x in zip(objs, xs):
        pos[o] = (float(x), -float(g))


def nodes(ax):
    cmap = plt.get_cmap("viridis")
    for o in order:
        col = "0.15" if gen[o] == 0 else cmap(gen[o] / maxg)
        ax.scatter(*pos[o], s=280, color=col, edgecolors="white",
                   linewidths=1.1, zorder=4)
        ax.text(*pos[o], o, ha="center", va="center", color="white",
                fontsize=8.5, fontweight="bold", zorder=5)
    ax.set_aspect("equal"); ax.axis("off")


def edge(ax, u, v, **kw):
    ax.plot([pos[u][0], pos[v][0]], [pos[u][1], pos[v][1]], zorder=2, **kw)


def main():
    fig, ax = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor("white")

    # A. parent-edges
    a = ax[0, 0]
    for ch, (p, q) in events.items():
        edge(a, ch, p, color="#3b6fb0", lw=1.4, alpha=0.7)
        edge(a, ch, q, color="#3b6fb0", lw=1.4, alpha=0.7)
    nodes(a)
    a.set_title("A. parent-edges  (child → its two operands)\n"
                "what the earlier analysis used — ternary reduced, direction imposed (§6.2)",
                fontsize=10)

    # B. 2-simplex (triangle per event)
    b = ax[0, 1]
    for ch, (p, q) in events.items():
        for u, v in ((ch, p), (ch, q), (p, q)):
            edge(b, u, v, color="#2a9d6f", lw=1.0, alpha=0.55)
    nodes(b)
    b.set_title("B. 2-simplex  (full triangle a—b—a/b)\n"
                "keeps the operand–operand edge the parent-edges dropped",
                fontsize=10)

    # C. operand-pairing only
    c = ax[1, 0]
    for ch, (p, q) in events.items():
        edge(c, p, q, color="#d1495b", lw=1.4, alpha=0.7)
    nodes(c)
    c.set_title("C. operand-pairing  (a—b only)\n"
                "connect the two distinguished; ignore the residue node",
                fontsize=10)

    # D. hypergraph: each slash = one 3-vertex hyperedge (shaded)
    d = ax[1, 1]
    cmap = plt.get_cmap("plasma")
    for k, (ch, (p, q)) in enumerate(events.items()):
        tri = np.array([pos[p], pos[q], pos[ch]])
        d.fill(tri[:, 0], tri[:, 1], color=cmap(k / len(events)), alpha=0.18,
               zorder=1)
    nodes(d)
    d.set_title("D. hypergraph  (each slash = one 3-vertex hyperedge {a,b,a/b})\n"
                "no reduction, no direction — the minimal honest reading",
                fontsize=10)

    fig.suptitle("By what criterion are the edges drawn?  The criterion is itself a Lens — "
                 "same skeleton, four graphs",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "the slash is a symmetric ternary incidence {a, b, a/b}; any binary "
             "graph chooses which pairs become edges.  The earlier free-graph chose "
             "A; the minimal one is D (the hypergraph).",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.045, 1, 0.95])
    out = "research-notes/geometric/connection_criterion.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
