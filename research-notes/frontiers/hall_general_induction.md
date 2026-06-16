# Frontier: Hall's marriage theorem, general `n`

`Combinatorics/HallMarriage` (this session) closed the framework + computed
matchings for `n ≤ 2`. The general-`n` Halmos–Vaughan induction is open.

## What is built (∅-axiom, reusable)
- `Matching` (injective `M : Fin n → Fin B` onto neighbors), `HallCond`,
  decidable counting `countB`/`cardS`/`cardN` + `anyAdj`.
- Transfer lemmas: `countB_mono`, `cardN_mono`, `countB_le_one_of_subsingleton`,
  `exists_of_countB_pos`, `countB_pos_of_exists`, `neighbor_exists`.
- Data-level neighbor finders: `scanNeighbor`/`computeNeighbor`/`scanAvoid`
  (+ specs), the `Option.get`-by-Hall-count idiom.
- Headline `hall_matching_{zero,one,two}` (the matching as an explicit function).

## What remains (the induction step)
The Halmos–Vaughan dispatch on `Fin (n+1)`:
- **Slack case** — every proper nonempty `S` has `cardN S > cardS S`: match
  vertex `0` to a neighbor `r0`, delete `(0, r0)`, show residual `HallCond` on the
  `Fin n` subgraph (each subset lost ≤ 1 neighbor but had strict slack), recurse.
- **Tight case** — some proper nonempty `S` has `cardN S = cardS S`: recurse on
  `S` into `N(S)`; recurse on the complement with neighbors outside `N(S)`
  (residual Hall by a counting argument); combine the two matchings.

The load-bearing gap is the **subgraph re-indexing**: after deleting a
left-vertex and a right-vertex, re-express the smaller bipartite graph over
`Fin n` / `Fin (B-1)` and re-derive `HallCond` on it from the parent's. The
counting lemmas above are the ingredients; the bookkeeping (a `Fin`-reindex that
stays ∅-axiom — no propext from `Fin` surgery) is the work.

## Selection note
Vein-B forcing case (the matching is computed by the augmenting recursion vs.
classical duality/LP existence). Logged in
`frontiers/pure_forces_different_proof.md` ("Hall's marriage theorem").
