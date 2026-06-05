"""The free-graph Lens — the minimal reading: only adjacency, no metric.

Drawing the "bare" Raw tree is itself a Lens — the free-graph Lens.  It reads the
slash as a graph: nodes = relation-objects, edges = "is the slash of these two".
It imposes the LEAST geometric content — only which pairs are connected — yet it
still imposes something (the graph), and any *drawing* of that graph adds an
arbitrary layout.  So even the most neutral reading is not the Raw: the Raw is
reached by none (`object1_not_surjective`).

This file looks around inside that Lens:

  A. the graph at small size, labelled — the actual combinatorial object.
  B,C. the SAME larger graph under two force-directed layouts (different seeds):
       different shapes, identical topology — the shape is the layout, not the Raw.
  D. the layout-INVARIANT readout: the birth-ordered adjacency matrix.  This —
     not any drawn shape — is what the free-graph Lens actually reads (each node
     bonds to its two earlier parents; the strictly lower-triangular, 2-per-row
     pattern is the slash's recursion made matrix).

Run:  python3 research-notes/geometric/free_graph_lens.py
"""

import numpy as np
import matplotlib.pyplot as plt

LETTERS = "abcdefghijklmnopqrstuvwxyz"


def build_graph(N):
    """Explosive Raw unfolding: each new object is the slash of a pair, then
    pairs with every existing object.  Returns edges (child→parent) and gen."""
    edges = []
    gen = [0, 0]            # a, b
    queue = [(0, 1)]
    nodes = 2
    qi = 0
    while nodes < N and qi < len(queue):
        i, j = queue[qi]; qi += 1
        c = nodes; nodes += 1
        edges.append((c, i)); edges.append((c, j))
        gen.append(max(gen[i], gen[j]) + 1)
        for m in range(c):          # pair the new node with all existing
            queue.append((c, m))
    return nodes, edges, gen


def spring(n, edges, seed, iters=400):
    rng = np.random.default_rng(seed)
    pos = rng.uniform(-1, 1, (n, 2))
    A = np.zeros((n, n))
    for i, j in edges:
        A[i, j] = A[j, i] = 1.0
    k = 0.7 / np.sqrt(n)
    for it in range(iters):
        delta = pos[:, None, :] - pos[None, :, :]
        dist = np.linalg.norm(delta, axis=2) + 1e-9
        rep = (k * k / dist ** 2)[:, :, None] * delta
        rep[np.arange(n), np.arange(n)] = 0
        disp = rep.sum(1)
        att = (dist / k)[:, :, None] * delta * A[:, :, None]
        disp -= att.sum(1)
        length = np.linalg.norm(disp, axis=1, keepdims=True) + 1e-9
        t = 0.08 * (1 - it / iters) + 0.001
        pos += disp / length * np.minimum(length, t)
    return pos


def draw(ax, pos, edges, gen, labels=False, s=120):
    cmap = plt.get_cmap("viridis")
    mg = max(gen)
    for c, p in edges:
        ax.plot([pos[c, 0], pos[p, 0]], [pos[c, 1], pos[p, 1]],
                color="0.7", lw=0.6, alpha=0.5, zorder=1)
    for v in range(len(pos)):
        col = "0.15" if gen[v] == 0 else cmap(gen[v] / mg)
        ax.scatter(*pos[v], s=s, color=col, edgecolors="white",
                   linewidths=0.8, zorder=3)
        if labels and v < len(LETTERS):
            ax.text(pos[v, 0], pos[v, 1], LETTERS[v], ha="center", va="center",
                    color="white", fontsize=8, fontweight="bold", zorder=4)
    ax.set_aspect("equal"); ax.axis("off")


def main():
    fig, axes = plt.subplots(2, 2, figsize=(14, 13))
    fig.patch.set_facecolor("white")

    # A. small labelled graph
    n1, e1, g1 = build_graph(12)
    draw(axes[0, 0], spring(n1, e1, 1), e1, g1, labels=True, s=300)
    axes[0, 0].set_title("A. the graph (small, labelled)\n"
                         "nodes = relation-objects, edges = slash-of-two",
                         fontsize=11)

    # B, C. same larger graph, two seeds
    n2, e2, g2 = build_graph(40)
    draw(axes[0, 1], spring(n2, e2, 2), e2, g2)
    axes[0, 1].set_title("B. force-directed layout (seed 2)\n"
                         "a self-organized shape", fontsize=11)
    draw(axes[1, 0], spring(n2, e2, 11), e2, g2)
    axes[1, 0].set_title("C. SAME graph, layout (seed 11)\n"
                         "different shape, identical topology — the shape is the Lens",
                         fontsize=11)

    # D. layout-invariant readout: adjacency matrix
    A = np.zeros((n2, n2))
    for i, j in e2:
        A[i, j] = A[j, i] = 1
    axes[1, 1].imshow(A, cmap="magma", origin="upper", interpolation="nearest")
    axes[1, 1].set_title("D. the layout-INVARIANT readout: adjacency matrix\n"
                         "each node bonds to its two earlier parents (the slash recursion)",
                         fontsize=11)
    axes[1, 1].set_xlabel("birth order", fontsize=9)
    axes[1, 1].set_ylabel("birth order", fontsize=9)

    fig.suptitle("The free-graph Lens — the minimal reading (only adjacency, no metric): "
                 "shape = layout (arbitrary), content = the graph (D)",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.02,
             "the free-graph Lens imposes the least — yet still a graph, and any "
             "drawing adds a layout.  Even the most neutral reading is not the Raw "
             "(reached by none, object1_not_surjective).",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.045, 1, 0.95])
    out = "research-notes/geometric/free_graph_lens.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
