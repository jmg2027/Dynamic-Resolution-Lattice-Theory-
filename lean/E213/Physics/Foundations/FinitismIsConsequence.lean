import E213.Math.Real213.DyadicTrajectory
import E213.Physics.Foundations.NUniverseFractalDepth

/-!
# Resolution-limit consequences — Cauchy trajectory ≠ exact value
under ∅-axiom

**핵심 명제** (canonical reading: `seed/RESOLUTION_LIMIT_SPEC.md` §1):
ZFC merges Cauchy-trajectory and putative exact-value objects via
`propext` / `Quot.sound` (quotient by Cauchy equivalence).  ∅-axiom
regime does not admit `propext` or `Quot.sound`, so the trajectory
and the exact-value live at distinct types and remain structurally
inequal.

This file packages the existing 0-axiom witnesses of that type
distinction.  The legacy theorem names (`completed_infinity_fails`,
`finitism_is_consequence`) are retained for stability of external
references; their content is type-distinction preservation, not
philosophical rejection of "completed infinity".

## Existing ∅-axiom witnesses (in repo)

  - `Real213DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero`:
      Cauchy-trajectory value at (0, 1) (= `false`) and exact-value
      at (0, 1) (= `true`) are structurally distinct under ∅-axiom.

  - `Real213DyadicTrajectory.zero_plus_gap_below_zero_exact`:
      Gap structurally preserved for all (0, k ≥ 1) — type
      distinction is universal across the boundary, not a single
      precision artifact.

## Resolution-limit framing

Per `RESOLUTION_LIMIT_SPEC.md` §3, the correct 213-internal reading:

  > Resolution limit is a structural invariant emerging from
  > four-domain convergence at d = 5.  Both potential infinity
  > (unbounded inductive trajectories) and constructive infinity
  > (Cantor tower, Bishop reals) are admitted; only completed-
  > infinity equality (limit = exact value via propext-quotient) is
  > structurally absent.

The constant `N_U = d^(d²) = 5²⁵` is a four-domain convergent
invariant (lens cardinality + K_{25} coloring + rank-2 tensor
DOF + injective projection space), not an axiomatic cap.
-/

namespace E213.Physics.Foundations.FinitismIsConsequence

open E213.Math.Real213.CutSum

/-- ★★★ Cauchy-trajectory ≠ exact value at type level under ∅-axiom
    (canonical: `RESOLUTION_LIMIT_SPEC.md` §1).  Legacy name retained. -/
theorem completed_infinity_fails :
    -- Cauchy limit at (0, 1) gives FALSE
    (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 1 = false
    -- Exact value at (0, 1) gives TRUE
    ∧ (constCut 0 1) 0 1 = true :=
  alwaysTrueUnit_limit_distinct_from_zero

/-- ★★★ Infinitesimal gap universal for boundary queries. -/
theorem infinitesimal_gap_universal :
    ∀ k, k ≥ 1 →
      (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 k = false
      ∧ (constCut 0 1) 0 k = true :=
  zero_plus_gap_below_zero_exact

/-- ★★★★★★★★★★ Resolution-limit type distinction — meta capstone.

  ZFC equality between Cauchy-trajectory and exact-value uses
  `propext` + `Quot.sound` to identify them; ∅-axiom regime does not
  admit either, so the type distinction is preserved.  This bundles
  the (0, 1) witness with the universal (0, k ≥ 1) family.
  Canonical reading: `seed/RESOLUTION_LIMIT_SPEC.md` §1.  Legacy name
  `finitism_is_consequence` retained for backward compatibility. -/
theorem finitism_is_consequence :
    ((ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 1 = false
     ∧ (constCut 0 1) 0 1 = true)
    ∧ (∀ k, k ≥ 1 →
         (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 k = false
         ∧ (constCut 0 1) 0 k = true) :=
  ⟨alwaysTrueUnit_limit_distinct_from_zero,
   zero_plus_gap_below_zero_exact⟩

end E213.Physics.Foundations.FinitismIsConsequence
