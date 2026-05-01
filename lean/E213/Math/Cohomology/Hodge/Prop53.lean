import E213.Math.Cohomology.Hodge.Star
import E213.Math.Cohomology.Universal.Prop53

/-!
# ⋆⋆ = id Prop-lift at (5, 3) — Δ⁴ 3-cochain stratum

Cochain 5 3 = Fin (binom 5 3) → Bool = Fin 10 → Bool, 1024
patterns × 10 indices = 10240 evaluations.  Same scale as (5, 2).

Closes the second-from-top stratum of the Hodge involution chain.
By Hodge duality binom 5 3 = binom 5 2 = 10, so the structure
parallels (5, 2).
-/

namespace E213.Math.Cohomology.Hodge.Prop53

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 5 3 parametrized (re-exported from UniversalProp53). -/
abbrev pattern53 := UniversalProp53.pattern

set_option maxHeartbeats 8000000 in
/-- ⋆⋆ = id on every (5, 3) pattern: 1024 patterns × 10 indices. -/
theorem hodge_sq_pattern_5_3 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ i : Fin (binom 5 3),
      hodgeStar 5 2 3
        (hodgeStar 5 3 2 (pattern53 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
        = pattern53 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 i := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 3, ⋆⋆σ = σ. -/
theorem hodge_sq_prop_5_3 (σ : Cochain 5 3)
    (i : Fin (binom 5 3)) :
    hodgeStar 5 2 3 (hodgeStar 5 3 2 σ) i = σ i := by
  rw [UniversalProp53.pattern_eq σ]
  exact hodge_sq_pattern_5_3 _ _ _ _ _ _ _ _ _ _ i

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 3). -/
theorem hodge_involution_capstone_5_3 :
    ∀ σ : Cochain 5 3, ∀ i : Fin (binom 5 3),
      hodgeStar 5 2 3 (hodgeStar 5 3 2 σ) i = σ i :=
  hodge_sq_prop_5_3

end E213.Math.Cohomology.Hodge.Prop53
