# Cohomology — Bipartite

**Status**: Closed.
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch).

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

## Lean source

- `lean/E213/Lib/Math/Cohomology/Bipartite/`
- ∅-axiom PURE on production critical path

## Connection

- `theory/math/cohomology/k32_higher_cohomology.md` — higher-cohomology
  structure (2/3/4-skeleton, Steenrod algebra, cup-i ladder)
- `theory/math/cohomology/cup_ladder_graduation.md` — physics
  application bridge (α_em residual via `(k+1)` graduation)
- `theory/math/cohomology/hodge_conjecture.md` — HodgeConjecture sub-tree (parent)
- Other cohomology sub-clusters cite this layer
