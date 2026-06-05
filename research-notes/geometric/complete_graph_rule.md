# "Line ↔ point, connect to all" → the complete graph → the simplex

*Tier 1.  Mingu Jeong's refined generative cycle and what it builds
(`complete_graph_rule.py`).*

## The rule (made precise)

- Two points.
- Cycle: draw the line(s) between points (중간 1); each line corresponds to one
  new point (중간 2 — **line ↔ point**, the slash: relation → object); the new
  point draws lines to every point it is **not already connected to** (중간 3).
- Repeat: each new line → a point; each new point → lines to all non-connected.

## What it is: the complete graph K_n (computed, exact)

At every stage the graph is the **complete graph** `K_n`.  Confirmed
computationally round by round (`edges = C(n,2)` exactly).  The reason: a new
point joins all then-existing points, and every later point joins back to it, so
each vertex ends adjacent to all others.  The "이어지지 않은" (only
non-already-connected) clause keeps it a *simple* graph and is exactly why it is
not a tree — it is the **maximally** not-a-tree object.  The branching worry is
correct, and its resolution is `K_n`.

## The growth

- point counts `n_k`: `2, 3, 5, 12, 68, 2280, 2 598 062, …`
- new points per round `= new lines of the previous round`: `1, 2, 7, 56, 2212, …`
- recursion `n_{k+1} = n_k + [C(n_k,2) − C(n_{k−1},2)]`, with the graph `= K_{n_k}`.
- growth `n_{k+1} ≈ C(n_k,2) ≈ n_k²/2` → **doubly exponential** (the
  configCount-style explosion, `Lib/Math/Cohomology/Fractal/ConfigCount`).

## Where it lands: the dimension-Lens / Δ^∞

`K_n` is the 1-skeleton of the regular `(n−1)`-simplex, so the limit `K_ω` is the
infinite simplex `Δ^∞` — exactly the **free / dimension-Lens** cell of the atlas
(`AngleStructure/SimplexOrthogonality.lean`).  Read off the rule: "line → point"
is the slash (relation becomes object); "connect to all non-connected" is the
free reading (every pair distinct and adjacent).  So this clean cycle is the
*generative engine* of the simplex reading — it derives **why** the free reading
builds the simplex.

## Relation to the connection-criterion dial

This resolves the earlier connection-criterion question at the maximal end.  The
sparse "parent-edge" graph joined each new point only to its two operands
(`|E| = 2(N−2)`, `√(2N)` hubs); this rule joins each new point to **all**
non-connected ones (`|E| = C(N,2)`, complete).  Same vertex generations
(`2,1,2,7,56,2212,…`), opposite ends of the dial: hypergraph (minimal) →
parent-edges (sparse) → **complete graph** (maximal, this rule).  The criterion is
the Lens; this description picks the complete-graph reading, and that reading is
the simplex.
