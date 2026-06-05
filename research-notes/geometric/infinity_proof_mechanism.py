"""How the infinite is proved, seen through the shapeLens.

§1.0′ (seed/AXIOM/01_residue.md): the primitive proof technique for the infinite
is DIAGONALIZATION, and diagonalization IS the residue — "given everything one can
point at (a totality), the something distinguishable from all of them is forced to
exist, and that forcing is the proof."  Cantor, Russell, Gödel, Turing, Tarski are
ONE move.  In the repo: `Lens/FlatOntologyClosure.object1_not_surjective`
(= `cantor_raw_bool`).

Seen through the `shapeLens` (point = object, line = relation):
  · the slash itself (the relation of two → a fresh object distinguishable from
    both) is the LOCAL diagonal: one new point outside the current two;
  · the Cantor diagonal is the slash read across a whole enumeration at once: the
    anti-diagonal point differs from every listed point, so it is outside the list;
  · iterating never closes (the generative graph has no final stage from inside) —
    that non-closure IS the diagonal IS the proof-engine for the infinite.

Run:  python3 research-notes/geometric/infinity_proof_mechanism.py
"""

import numpy as np
import matplotlib.pyplot as plt


# ---- A. the Cantor grid: enumerate all rows; flip the diagonal -> outside ----
def panel_grid(ax, n=9, seed=2):
    rng = np.random.default_rng(seed)
    M = rng.integers(0, 2, (n, n))
    ax.imshow(M, cmap="Greys", vmin=-0.3, vmax=1.3, origin="upper")
    for i in range(n):
        ax.add_patch(plt.Rectangle((i - 0.5, i - 0.5), 1, 1, fill=False,
                                   edgecolor="#d1495b", lw=2.2, zorder=3))
    # the anti-diagonal point d (= flip of the diagonal), drawn below
    d = 1 - np.diag(M)
    for j in range(n):
        ax.add_patch(plt.Rectangle((j - 0.5, n + 0.5 - 0.5), 1, 1,
                                   color=("0.15" if d[j] else "white"),
                                   ec="#d1495b", lw=1.5, zorder=3))
        ax.text(j, n + 0.5, "¬", ha="center", va="center", fontsize=7,
                color=("white" if d[j] else "#d1495b"))
    ax.text(n + 0.2, n + 0.5, "d = ¬diag", color="#d1495b", fontsize=9, va="center")
    for i in range(n):
        ax.annotate("", xy=(i, n + 0.1), xytext=(i, i + 0.35),
                    arrowprops=dict(arrowstyle="->", color="#d1495b", lw=0.7,
                                    alpha=0.5))
    ax.set_title("A. enumerate every point (row); flip the diagonal\n"
                 "d differs from row i at column i ⟹ d is NO listed point",
                 fontsize=10)
    ax.set_xlim(-0.6, n + 1.5); ax.set_ylim(n + 1.2, -0.6); ax.axis("off")


# ---- B. the slash as the local diagonal; the graph never closes -------------
def panel_slash(ax):
    # generative unfolding: each new point = relation of two = fresh, outside prior
    parents = {"c": ("a", "b"), "d": ("c", "a"), "e": ("c", "b"),
               "f": ("d", "e"), "g": ("d", "c"), "h": ("e", "c")}
    seeds = ["a", "b"]
    order = seeds + list(parents)
    gen = {"a": 0, "b": 0}
    for ch, (x, y) in parents.items():
        gen[ch] = max(gen[x], gen[y]) + 1
    mg = max(gen.values())
    pos = {}
    byg = {}
    for o in order:
        byg.setdefault(gen[o], []).append(o)
    for g, objs in byg.items():
        xs = [0.0] if len(objs) == 1 else np.linspace(-1, 1, len(objs))
        for o, x in zip(objs, xs):
            pos[o] = (float(x), -float(g))
    cmap = plt.get_cmap("viridis")
    for ch, (x, y) in parents.items():
        for p in (x, y):
            ax.plot([pos[ch][0], pos[p][0]], [pos[ch][1], pos[p][1]],
                    color="0.7", lw=0.9, alpha=0.5, zorder=1)
    for o in order:
        newest = gen[o] == mg
        col = "#d1495b" if newest else ("0.15" if gen[o] == 0 else cmap(gen[o] / mg))
        ax.scatter(*pos[o], s=360, color=col, edgecolors="white", linewidths=1.2,
                   zorder=3)
        ax.text(*pos[o], o, ha="center", va="center", color="white", fontsize=9,
                fontweight="bold", zorder=4)
    ax.text(0, -mg - 0.8,
            "each new point a/b is distinguishable from a AND b (the slash) —\n"
            "the LOCAL diagonal; the frontier (red) is always outside the prior set;\n"
            "the graph never closes from inside (object1_not_surjective)",
            ha="center", fontsize=8.5, color="0.25")
    ax.set_title("B. through the shapeLens: the slash = the local diagonal",
                 fontsize=10)
    ax.set_xlim(-1.3, 1.3); ax.set_ylim(-mg - 1.3, 0.5); ax.axis("off")


# ---- C. the one move: five theorems, one skeleton ---------------------------
def panel_onemove(ax):
    ax.axis("off")
    ax.set_title("C. one move:  d(x) = ¬ cover(x)(x)  — the anti-diagonal residue",
                 fontsize=10)
    rows = [
        ("Cantor", "reals as a list", "a real flipping the n-th digit of the n-th"),
        ("Russell", "sets, ∈ as cover", "R = {x : x ∉ x}"),
        ("Gödel", "proofs, Prov as cover", "G = “G is unprovable”"),
        ("Turing", "machines, halt as cover", "the diagonal non-halting machine"),
        ("Tarski", "sentences, True as cover", "the liar “this is false”"),
        ("213", "Object1 : Raw→(Raw→Bool)", "λr. ¬Object1 r r  (cantor_raw_bool)"),
    ]
    y = 0.88
    ax.text(0.02, 0.98, "theorem", fontsize=8.5, fontweight="bold", color="0.3")
    ax.text(0.30, 0.98, "totality / self-cover", fontsize=8.5, fontweight="bold",
            color="0.3")
    ax.text(0.66, 0.98, "the anti-diagonal residue (outside the image)",
            fontsize=8.5, fontweight="bold", color="0.3")
    for name, cov, res in rows:
        c = "#d1495b" if name == "213" else "0.15"
        ax.text(0.02, y, name, fontsize=8.5, color=c, fontweight="bold")
        ax.text(0.30, y, cov, fontsize=8, color="0.3")
        ax.text(0.66, y, res, fontsize=8, color=c)
        y -= 0.13
    ax.text(0.5, -0.02,
            "the cover is a self-map T → (T→2); the residue r(x)=¬cover(x)(x) is in\n"
            "the codomain but not the image — forced to exist, and the forcing IS the proof",
            ha="center", fontsize=8.5, color="#3b6fb0")
    ax.set_xlim(0, 1); ax.set_ylim(-0.12, 1.02)


def main():
    fig = plt.figure(figsize=(16, 11))
    fig.patch.set_facecolor("white")
    a = fig.add_subplot(2, 2, 1); panel_grid(a)
    b = fig.add_subplot(2, 2, 2); panel_slash(b)
    c = fig.add_subplot(2, 1, 2); panel_onemove(c)
    fig.suptitle("How the infinite is proved, through the shapeLens: "
                 "the residue is the diagonal is the slash (§1.0′)",
                 fontsize=14, fontweight="bold")
    fig.text(0.5, 0.005,
             "point at the totality (a self-cover), exhibit the something distinguishable "
             "from all of it (the residue) — that is the slash, the diagonal, and the "
             "primitive proof for the infinite, all one move.",
             ha="center", fontsize=10, color="0.3")
    fig.tight_layout(rect=[0, 0.03, 1, 0.95])
    out = "research-notes/geometric/infinity_proof_mechanism.png"
    fig.savefig(out, dpi=150, facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
