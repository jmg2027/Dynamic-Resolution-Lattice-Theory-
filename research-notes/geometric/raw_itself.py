"""Raw itself — the bare slash tree, before any reading.

Every panel of the atlas is a *Lens reading* of the slash: a combining map that
places the relation-objects somewhere.  This file steps back to the Raw itself:
the residue family `a, b, a/b, a/(a/b), …` (02_axiom.md §2.2), the inductive
`Tree | a | b | slash` (`Theory/Raw/Slash.lean`) — the bare combinatorial
skeleton of distinguishings, the same tree Mingu Jeong's first sketch unfolded
(`a, b → c → d, e → f..q → …`).

The honest paradox: Raw commits to no geometry (§2.5), so any *placement* of its
nodes is already a Lens.  The Raw as-such is the residue reached by no reading
(`FlatOntologyClosure.object1_not_surjective`); the pictures below are charts of
it (§6.2), not it.  What is invariant is the skeleton (which node is the slash of
which); what changes panel to panel is only the embedding.

  Left  — the bare Raw tree, one neutral layout, labelled with the Raw terms.
  Right — the SAME skeleton under four embeddings (betweenness / free / mediant /
          random): one Raw, many readings; the positions are the Lens.

Run:  python3 research-notes/geometric/raw_itself.py
"""

import numpy as np
import matplotlib.pyplot as plt

# the bare Raw unfolding (= the first-sketch tree).  parents[x] = (y, z): x = y/z.
parents = {
    "c": ("a", "b"),
    "d": ("c", "a"), "e": ("c", "b"),
    "f": ("d", "a"), "g": ("d", "b"), "h": ("d", "c"), "i": ("d", "e"),
}
SEEDS = ["a", "b"]
order = SEEDS + list(parents.keys())

gen = {"a": 0, "b": 0}
for ch, (x, y) in parents.items():
    gen[ch] = max(gen[x], gen[y]) + 1
by_gen = {}
for o in order:
    by_gen.setdefault(gen[o], []).append(o)
maxg = max(gen.values())


def draw_edges(ax, pos, col="0.6"):
    for ch, (x, y) in parents.items():
        for p in (x, y):
            ax.plot([pos[ch][0], pos[p][0]], [pos[ch][1], pos[p][1]],
                    color=col, lw=0.9, alpha=0.55, zorder=1)


def draw_nodes(ax, pos, labels=True, s=320):
    cmap = plt.get_cmap("viridis")
    for o in order:
        x, y = pos[o]
        col = "0.15" if gen[o] == 0 else cmap(gen[o] / maxg)
        ax.scatter([x], [y], s=s, color=col, edgecolors="white",
                   linewidths=1.2, zorder=3)
        if labels:
            ax.text(x, y, o, ha="center", va="center", color="white",
                    fontsize=9, fontweight="bold", zorder=4)


# ----- the four embeddings (each is a Lens) ----------------------------------
def layout_hierarchical():
    pos = {}
    for g, objs in by_gen.items():
        n = len(objs)
        xs = [0.0] if n == 1 else np.linspace(-1, 1, n)
        for o, x in zip(objs, xs):
            pos[o] = (float(x), -float(g))
    return pos


def layout_betweenness():
    # dyadic value on [0,1] (the midpoint reading), y = -generation
    val = {"a": 0.0, "b": 1.0}
    for ch, (x, y) in parents.items():
        val[ch] = 0.5 * (val[x] + val[y])
    return {o: (val[o], -gen[o]) for o in order}


def layout_free():
    # each generation on its own ring, spread by angle (the free/orthogonal read)
    pos = {}
    for g, objs in by_gen.items():
        n = len(objs)
        ang = np.linspace(0.15 * np.pi, 0.85 * np.pi, n) if n > 1 else [0.5 * np.pi]
        for o, a in zip(objs, ang):
            r = g + 0.6
            pos[o] = (r * np.cos(a), r * np.sin(a))
    pos["a"], pos["b"] = (-0.4, 0.0), (0.4, 0.0)
    return pos


def layout_random():
    rng = np.random.default_rng(3)
    return {o: (float(rng.normal()), float(rng.normal())) for o in order}


def main():
    fig = plt.figure(figsize=(16, 7.5))
    fig.patch.set_facecolor("white")

    # left: the bare Raw tree
    axL = fig.add_subplot(1, 2, 1)
    posH = layout_hierarchical()
    draw_edges(axL, posH)
    draw_nodes(axL, posH)
    # annotate the Raw terms for the first nodes
    terms = {"c": "a/b", "d": "c/a", "e": "c/b"}
    for o, t in terms.items():
        x, y = posH[o]
        axL.text(x + 0.06, y, f"= {t}", fontsize=8, color="0.4", va="center")
    axL.set_title("Raw itself — the residue family  a, b, a/b, …  (§2.2)\n"
                  "the bare slash tree (= the first sketch a,b→c→d,e→f..q)",
                  fontsize=12)
    axL.axis("off")

    # right: the same skeleton under four Lenses
    inner = [("betweenness (midpoint)", layout_betweenness()),
             ("free (orthogonal)", layout_free()),
             ("mediant-style", layout_betweenness()),
             ("random", layout_random())]
    # replace mediant-style with a skewed layout to differ visibly
    val = {"a": 0.0, "b": 1.0}
    for ch, (x, y) in parents.items():
        val[ch] = (2 * val[x] + val[y]) / 3.0  # asymmetric "mediant-ish" skew
    inner[2] = ("mediant-style (skew)", {o: (val[o], -gen[o]) for o in order})

    for k, (name, pos) in enumerate(inner):
        ax = fig.add_subplot(2, 4, (3 if k < 2 else 7) + (k % 2))
        draw_edges(ax, pos, col="0.7")
        draw_nodes(ax, pos, labels=False, s=70)
        ax.set_title(name, fontsize=9)
        ax.axis("off")

    fig.text(0.74, 0.045,
             "one Raw, four readings — the skeleton is invariant, the positions "
             "are the Lens.\nRaw commits to no geometry (§2.5); the Raw as-such is "
             "reached by none (object1_not_surjective).",
             ha="center", fontsize=8.5, color="0.3")
    fig.suptitle("the Raw and its readings — every atlas shape is this one tree, embedded",
                 fontsize=13, fontweight="bold")
    fig.tight_layout(rect=[0, 0.06, 1, 0.95])
    out = "research-notes/geometric/raw_itself.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
