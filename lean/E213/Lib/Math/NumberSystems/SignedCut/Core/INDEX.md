# `SignedCut/Core/` — signed Real213 cut algebra

Signed-cut (negative-valued Real213) core: type, equivalence,
algebraic structure, inverse, Cauchy convergence.

## Files (9)

  - `Core.lean`               — `SignedCut` carrier
  - `Equivalence.lean`        — signed-cut equivalence
  - `Algebra.lean`            — add / sub / mul algebraic structure
  - `Inv.lean`                — inverse construction
  - `UnifiedGenericInv.lean`  — unified generic inverse
  - `CauchyConvergence.lean`  — Cauchy convergence witness
  - `MulRuleCapstone.lean`    — multiplication-rule capstone
  - `MathClosureCapstone.lean`— math-closure capstone
  - `Capstone.lean`           — SignedCut top capstone

## Companion sub-clusters (in `SignedCut/`)

  - `CD/`       — Cayley-Dickson level applications
  - `Hurwitz/`  — Hurwitz integer signed variant
  - `Level/`    — level-tower analogues
  - `Bridge/`   — bridges to other clusters
  - `Octonion/` — octonion signed variant

## Where to add new files

  - New algebra / op       → `Algebra` or `<op>.lean`
  - Inverse refinement     → `Inv` / `UnifiedGenericInv`
  - Convergence proof      → `CauchyConvergence` / `<...>Capstone`
