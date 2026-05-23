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

## Open frontier

The fully universal Nat-quantified theorem

```
∀ (NS NT c : Nat), 1 ≤ NS → 1 ≤ NT → 1 ≤ c →
  kerSizeDelta0Direct NS NT c = 2
```

is not yet proved.  It requires a graph-walk connectedness
induction over arbitrary K_{NS,NT}^{(c)} — `lean/E213/` does not
yet host a `GraphWalk/` infrastructure of the needed shape.

Extending the parametric coverage to chartBase ≥ 6 (current
explicit `decide`-checks stop at chartBase 5) is the smaller
extension; the universal Nat-theorem is the larger.

## Connection

- `theory/math/cohomology/k32_higher_cohomology.md` — higher-cohomology
  structure (2/3/4-skeleton, Steenrod algebra, cup-i ladder)
- `theory/math/cohomology/cup_ladder_graduation.md` — physics
  application bridge (α_em residual via `(k+1)` graduation)
- `theory/math/cohomology/hodge_conjecture.md` — HodgeConjecture sub-tree (parent)
- `theory/math/geometrization_conjecture.md` — KChartLensAbstract +
  K-deployment family enumeration (consumer of
  `parametric_close_capstone`)
