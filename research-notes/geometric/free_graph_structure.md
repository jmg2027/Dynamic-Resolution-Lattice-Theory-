# How the free-graph Lens's Raw graph is built — precise structure

*Tier 1.  A precise combinatorial analysis of the graph the free-graph Lens reads
off the slash (`free_graph_lens.py`, `free_graph_analysis.py`).  Nodes =
relation-objects, edges = "is the slash of these two".*

## The build (closed form, no queue)

Seeds `a = 0`, `b = 1`; node `2 = a/b`.  Thereafter a node `X (≥2)` — a
**spawner** — is the first parent of children paired with every earlier
`m = 0..X−1`, in birth order.  This is exactly the first-sketch unfolding; it
needs no `O(N²)` queue, because the order is deterministic:

> Block `X (≥2)` occupies nodes `[2 + (X−1)X/2, 1 + X(X+1)/2]`.
> Node `c` in that block has parents `(X, m)` with `m = c − (2 + (X−1)X/2)`.

Verified equal to the queue construction for all `c < 60`.

## The exact laws (measured, confirmed to `N = 10⁶`)

- **Edges.**  `|E| = 2(N−2)` exactly.  Every non-seed node has **out-degree
  exactly 2** — it is the slash of exactly two earlier objects.  This is the
  axiom's arity-2 (`02_axiom.md`, the binary slash) made graph-regular; mean
  degree `2|E|/N → 4`.

- **Spawner blocks.**  Spawner `X` has exactly `X` children (as first parent);
  cumulative nodes born through spawner `X` is `2 + X(X+1)/2` — **quadratic**.
  Hence at `N` nodes the current spawner is `X ≈ √(2N)`.

- **Hubs.**  The number of nodes with degree `> 2` is `≈ √(2N)`, and the
  **maximum degree is `≈ √(2N)`** (ratio measured `1.051 → 1.001` as
  `N : 10³ → 10⁶`).  The oldest nodes — `a, b` and the small indices — bond to
  all `√(2N)` active spawners (as second parent), so they are the hubs.

- **Leaf-dominated.**  The fraction of degree-2 nodes `→ 1`
  (`95.4% → 99.86%` as `N : 10³ → 10⁶`): almost every node is a freshly-born
  terminal that has not yet spawned.

- **Bimodal degree distribution.**  Not a power law: the degrees split into the
  `~√(2N)` hubs (all clustered near degree `√(2N)`) and the overwhelming mass of
  degree-2 leaves.  A deterministic two-scale structure, not preferential
  attachment.

- **Generations explode.**  Generation sizes are hyper-exponential (at
  `N = 3000`: gen sizes `2, 1, 2, 7, 56, 2212, …`) — the configCount-style
  explosion (`Lib/Math/Cohomology/Fractal/ConfigCount`).

## The 213 reading

The graph's two invariants name two axiom facts.  **Out-degree 2 everywhere** is
the slash's binary arity: each object *is* the relation of exactly two.  And the
**hubs are the oldest distinguishings** — `a, b` are referenced by the most
later relations, decaying to the degree-2 leaves of the youngest — so "older
residue is pointed at more" is a measured law, not a metaphor.  Crucially these
are properties of the *graph* (a predicate on `Raw²`, §6.3 flat ontology), i.e.
of the free-graph **Lens** — the layout-invariant content of one reading, still
not the Raw as-such (`object1_not_surjective`).

## Open frontier

The out-degree-2 regularity (`|E| = 2(N−2)`) and the spawner-block identity
(spawner `X` has `X` children; cumulative `2 + X(X+1)/2`) are clean enough to
state ∅-axiom over `Nat` (the closed-form parent map and the block-size sum).
The `√(2N)` degree law is asymptotic and would need the `Real213`/inequality
machinery.  Not yet formalized.
