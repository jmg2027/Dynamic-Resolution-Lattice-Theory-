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

A **parametric V32Betti sub-tree** lifts the (NS, NT, c) = (3, 2, 2)
specialisation to the whole K_{NS,NT}^{(c)} deployment family:
Euler characteristic `(NS + NT) − c·NS·NT`, b_1 formula
`c·NS·NT + 1 − (NS + NT)` for the connected case, and δ⁰ kernel
size = 2 (b_0 = 1) verified across the chartBase-≤-5 deployment
range via `decide`.

## Lean source

- Sub-tree: `lean/E213/Lib/Math/Cohomology/Bipartite/`
  - `V32Betti.lean` — (3, 2, 2)-specific cohomology + b_1 = 8
  - `Filled3Cell*.lean`, `FaceCup*.lean`,
    `SteenrodSquaresAtOmega.lean`, `AdemUniversal.lean`,
    `CartanAtTruncation.lean`, `Filled4CellExtension.lean`,
    `SelfPairingTrace.lean` — higher-cohomology + Steenrod algebra
    at K_{3,2}^{(c=2)}
  - `Parametric/{CochSpaces, Delta0AndConnectedness,
    EulerAndCapstone}.lean` — parametric (NS, NT, c)-family
    cohomology; capstone `parametric_close_capstone` bundles the
    deployment-family invariants
  - `Parametric/KernelConstancyUniversal.lean` — universal
    (∀ NS NT c) structural δ⁰-kernel = constant cochains
- ∅-axiom PURE on production critical path

## Parametric V32Betti — deployment-family closure

`Parametric/CochSpaces.lean` defines `CochV NS NT` (vertex
cochains, `Fin (NS + NT) → Bool`) and `CochE NS NT c` (edge
cochains, `Fin (c·NS·NT) → Bool`) together with parametric
`srcOf`, `tgtOf`, `delta0` that specialise to the (3, 2, 2)
versions in `V32Betti.lean`.

`Delta0AndConnectedness.lean` verifies `ker(δ⁰) = 2` (i.e.
b_0 = 1) by `decide` across:

- Trees: K_{1,1}, K_{1,2}, K_{2,1}, K_{1,3}, K_{3,1}, K_{1,4}, K_{4,1}
- 4-cycles: K_{2,2}^{(c=1)}, K_{2,2}^{(c=2)}
- Forced critical: K_{3,2}^{(c=2)}, K_{2,3}^{(c=2)} (S/T swap)
- Higher chartBase: K_{3,3}^{(c=2)}

`EulerAndCapstone.lean` gives the parametric Euler / b_1 formulae
and bundles the closure as `parametric_close_capstone` — Euler at
(3, 2, 2) is −7, b_1 at (3, 2, 2) is 8 matching V32Betti exactly,
b_1 = 0 at tree deployments, kernel-size compatibility with the
specialisation.

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

The flat enumeration form
`∀ NS NT c, kerSizeDelta0Direct NS NT c = 2` stays `decide`-only at
the chartBase-≤-5 range: counting flat indices forces core Lean's
`Nat.div` / `Nat.mod` lemmas, all of which carry `propext`, so the
quantified-flat statement is axiom-dirty by Lean-core construction
— a purity artifact, not a mathematical gap, with the structural
content fully closed above.  The product-form kernel matches the
flat-form kernel on each concrete deployment (`decide` in
`Delta0AndConnectedness`).

The chart-axis consumer `forcedKChartLens` /
`m2_universal_forced_partition`
(`Geometry/GeometrizationConjecture/KChartLensAbstract.lean`) feeds
this 1-dimensional kernel into the axes partition, forcing
`selfPointingAxes = 1` and `chartVisibleAxes = chartBase − 1` for
arbitrary connected K.

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
- `theory/math/cohomology/hodge_conjecture.md` — HodgeConjecture sub-tree (parent)
- `theory/math/geometry/geometrization_conjecture.md` — KChartLensAbstract +
  K-deployment family enumeration (consumer of
  `parametric_close_capstone`)
