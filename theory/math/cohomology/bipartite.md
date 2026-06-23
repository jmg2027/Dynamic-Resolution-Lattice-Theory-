# Cohomology — Bipartite

**Status**: Closed.

## Overview

K_{3,2}^{(c=2)} bipartite multigraph cohomology.  b_0 = 1,
b_1 = 8 = NS² − 1 (= 1/α_3 = SU(3) gluon octet) at the
1-skeleton; b_1 = 6, b_2 = 1 at full simple-cycle filling
(2-skeleton).

The 2-skeleton's b_2 = 1 class ω = (1, 1, 1) is the unique
Sym(3)-invariant 2-cocycle; cohomology at the 3-skeleton + 4-skeleton
truncations and the Steenrod ladder at ω (Sq⁰/Sq¹, cup_1/cup_2 face
ladder, Steenrod-Whitehead bridge `cup_1(ω, ω) = δ²(ω)`) are
developed in `k32_higher_cohomology.md`.

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
  (`isKer_iff_const`, `isKer_const_false_or_true`,
  `isKer_root_determines`, `visible_plus_one`: visible dim
  `(NS + NT) − 1`)

### First Betti number `b₁ = E − V + 1` (parametric)

The first Betti number is the parametric formula
`b1Formula NS NT c = c·NS·NT + 1 − (NS + NT)`
(`EulerAndCapstone.b1Formula`), the `E − V + 1` count for a connected
deployment with `E = c·NS·NT` edges and `V = NS + NT` vertices.  At the
presentation `c = 2` of `K_{NS,NT}^{(c)}`:

  - `b1Formula 3 2 2 = 8 = NS² − 1 = 1/α₃` (`b1Formula_K32`, `decide`);
  - `eulerChar 3 2 2 = (NS + NT) − c·NS·NT = −7` (`eulerChar_K32`);
  - `eulerChar = 1 − b₁` across the family
    (`eulerChar_eq_one_sub_b1_family`).

The `c` here is a free presentation choice (it re-presents `NS² − 1`),
not a forced datum.  The tree deployments give `b₁ = 0`, and
`kerSize = 2` holds across the family — all bundled in
`parametric_close_capstone`.

The connectedness fact behind `b₀ = 1` is also reached through the abstract
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
