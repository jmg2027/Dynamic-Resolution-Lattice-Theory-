# Cohomology — Bipartite

**Status**: Closed.

## Overview

K_{3,2}^{(c=2)} bipartite multigraph cohomology.  b_0 = 1,
b_1 = 8 = NS² − 1 (= 1/α_3 = SU(3) gluon octet) at the
1-skeleton; b_1 = 6, b_2 = 1 at full simple-cycle filling
(2-skeleton).

The 2-skeleton's b_2 = 1 class ω = (1, 1, 1) is the unique
Sym(3)-invariant 2-cocycle; cohomology at the 3-skeleton + 4-skeleton
truncations and Steenrod-algebra structure (Sq^i, Adem, Cartan,
cup_i ladder, Steenrod-Whitehead bridge `cup_1(ω, ω) = δ²(ω)`)
are developed in `k32_higher_cohomology.md`.

The whole result is **carrier-free**: there is no 12-edge
K_{3,2}^{(c=2)} graph file.  The b_0 = 1 / b_1 = 8 content lives
in the **parametric (NS, NT, c) family**: Euler characteristic
`(NS + NT) − c·NS·NT`, b_1 formula `c·NS·NT + 1 − (NS + NT)` for
the connected case, and the structural δ⁰ kernel = constants
(b_0 = 1) for *every* connected deployment.

## Lean source

- Sub-tree: `lean/E213/Lib/Math/Cohomology/Bipartite/`
  - `Parametric/{CochSpaces, Delta0AndConnectedness,
    EulerAndCapstone}.lean` — parametric (NS, NT, c)-family
    cohomology; capstone `parametric_close_capstone` bundles the
    deployment-family invariants (b_1 at (3, 2, 2) = 8 via
    `b1Formula 3 2 2`; ker δ⁰ = 2 via `kerSizeDelta0Direct`)
  - `Parametric/Betti/KernelConstancyUniversal.lean` — universal
    (∀ NS NT c) structural δ⁰-kernel = constant cochains
    (`universal_kernel_close`)
  - `Filled3Cell*.lean`, `FaceCup*.lean`,
    `SteenrodSquaresAtOmega.lean`, `Filled4CellExtension.lean`,
    `SelfPairingTrace.lean` — higher-cohomology + Steenrod algebra
    over the type alias `CochE = Fin 12 → Bool` (no graph carrier)
  - `MultParityOrthogonal.lean` — multiplicity parity ℤ/2 ⊥
    cup-orientation ℤ/2 (refutes frontier P3′), over the parametric
    `srcOf`/`tgtOf` encoding
- ∅-axiom PURE on production critical path

## Parametric family — deployment-family closure

`Parametric/CochSpaces.lean` defines `CochV NS NT` (vertex
cochains, `Fin (NS + NT) → Bool`) and `CochE NS NT c` (edge
cochains, `Fin (c·NS·NT) → Bool`) together with parametric
`srcOf`, `tgtOf`, `delta0`; the (3, 2, 2) specialisation recovers
the K_{3,2}^{(c=2)} numbers (12 edges, 5 vertices) as theorems.

`Delta0AndConnectedness.lean` verifies `ker(δ⁰) = 2` (i.e.
b_0 = 1) by `decide` across:

- Trees: K_{1,1}, K_{1,2}, K_{2,1}, K_{1,3}, K_{3,1}, K_{1,4}, K_{4,1}
- 4-cycles: K_{2,2}^{(c=1)}, K_{2,2}^{(c=2)}
- Critical deployment (at presentation c=2): K_{3,2}^{(c=2)}, K_{2,3}^{(c=2)} (S/T swap)
- Higher chartBase: K_{3,3}^{(c=2)}

`EulerAndCapstone.lean` gives the parametric Euler / b_1 formulae
and bundles the closure as `parametric_close_capstone` — Euler at
(3, 2, 2) is −7, b_1 at (3, 2, 2) is 8, b_1 = 0 at tree
deployments, kernel-size = 2 across the family.

## Universal kernel = constants (structural b_0 = 1)

`KernelConstancyUniversal.lean` proves, ∅-axiom, for **every**
connected deployment (NS ≥ 1, NT ≥ 1, c ≥ 1):

```
ker δ⁰  =  { the two constant cochains }
```

— so `dim ker δ⁰ = 1` (b_0 = 1, the graph is connected) and
`dim im δ⁰ = (NS + NT) − 1` for all (NS, NT, c) at once, not just
the `decide`-checked range above.

The coboundary is taken in product-indexed form `delta0Tri`
(edges as triples `(i, j, m) : Fin NS × Fin NT × Fin c`), which
indexes the same graph as the flat `Fin (c·NS·NT)` form but needs
no integer-decode division — so the connectedness argument (every
S-vertex joins T-vertex 0, every T-vertex joins S-vertex 0, roots
joined) runs with zero `propext`.  Key theorems:

- `isKer_iff_const` — kernel cochain ⟺ globally constant
- `isKer_const_false_or_true` — kernel = exactly the 2 constants
- `isKer_root_determines` — root colour is the single free
  parameter (`dim ker = 1`)
- `universal_kernel_close` — the four facts bundled

The **flat-operator** form of the same result is
`KerSizeUniversal.ker_iff_constant`:
`(∀ e, CochSpaces.delta0 σ e = false) ↔ (∀ i j, σ i = σ j)` for the
canonical flat coboundary (edges `Fin (c·NS·NT)`), ∅-axiom — its
integer edge-decode uses the repo's pure division library
`Meta.Nat.NatDiv213`, the propext-free replacements for core `Nat.div` /
`Nat.mod`.  So the universal kernel = constants holds on the flat
operator directly; the product-indexed `KernelConstancyUniversal` is the
division-free companion that carries the count-form lemmas and the
graph-connectedness instantiation.

### Universal first Betti number `b₁ = E − V + 1`

`BettiOneUniversal.lean` (`betti_one_universal`) assembles the first
Betti number from ∅-axiom cardinalities counted via
`Combinatorics.BoolEnum` (cochains as `List Bool`, count by
`List.length` — no `Fintype`, `funext`, or `Nat.div`):

  - `|C⁰| = 2^V`        (`allBoolLists_length`),
  - `|ker δ⁰| = 2`      (`bcount_const`; kernel ⟺ constant) — `dim ker = 1`,
  - `|im δ⁰| = 2^(V−1)` (`bcount_headFalse`) — `dim im = V − 1`.

The `2^(V−1)` is an **actually-counted image cardinality of the genuine
K_{NS,NT} coboundary**, fully ∅-axiom.  The general count
`PathCoboundary.im_count_inj_complement` (`|im f| = 2^(V−1)` for any
complement-invariant, head-`false`-injective `f` — rank–nullity
`2^V/2` realised combinatorially) is instantiated in `KEdgeCochain` at the
list-valued complete-bipartite coboundary `edgeCochain NS NT σ = [σ[s] ⊕
σ[NS+t] : s<NS, t<NT]`.  Its two hypotheses are proven directly on lists:
`edgeCochain_complement` ((¬a)⊕(¬b) = a⊕b) and `edgeCochain_inj_headFalse`
(equal edge values force `σ ⊕ τ` constant across the adjacency;
head-`false` pins it to all-`false`).  So `KEdgeCochain.im_edgeCochain_card`
gives `|im δ⁰_K| = 2^(V−1)` — no `funext`, `Fintype`, `Nat.div`, or cited
bridge (`im_pathDelta_card` is the path-graph instance; `|im|` is
`c`-independent, the `c=1` edge set suffices).  The rank relations are
then exact ∅-axiom arithmetic (`2^(m+1) = 2 · 2^m`,
`2^E = 2^(V−1) · 2^{b₁}` with `E = (V−1) + b₁`), giving
`dim H¹ = b₁ = E − V + 1`.  At the presentation `c=2` of `K_{NS,NT}^{(c)}`
(`betti_one_K32`, `im_edgeCochain_K32` = `2^4`): `V = 5`, `E = 12`,
`b₁ = 8 = NS² − 1 = 1/α₃` — the `c` here a free presentation choice (it
re-presents `NS²−1`), not a forced datum.

The same conclusion is also reached through the abstract
graph-connectedness induction of
`theory/math/combinatorics/graph_connectivity.md`
(`Combinatorics/GraphConnectivity.lean`): the inductive reachability
predicate `Reach` + `closed_const` give "δ⁰-closed colouring on a
connected graph is constant" for any adjacency, and the bipartite
instantiation (`bipAdj_connected`, `isKer_const_via_framework`)
supplies the only graph-specific fact — that K_{NS,NT}^{(c)} is
connected.

## Connection

- `theory/math/cohomology/k32_higher_cohomology.md` — higher-cohomology
  structure (2/3/4-skeleton, Steenrod algebra, cup-i ladder)
- `theory/math/cohomology/cup_ladder_graduation.md` — physics
  application bridge (α_em residual via `(k+1)` graduation)
- `theory/math/cohomology/hodge.md` — cup-chain cohomology + ⋆⋆ involution
