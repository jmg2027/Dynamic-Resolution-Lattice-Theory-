import E213.Math.Cohomology.Universal.Core.Prop51

/-!
# ⋆⋆ = id Prop-lift at (5, 1) and (5, 2)

User: hard deferred items 될때까지 고고.  Same pattern
technique as Universal δ²=0 lifts ⋆⋆ = id from concrete
cochains to Prop-level ∀ σ.
-/

namespace E213.Math.Cohomology.HodgeProp

open E213.Physics.Simplex (binom)

/-- Cochain 5 1 parametrized (re-exported from UniversalProp51). -/
abbrev pattern51 := UniversalProp51.pattern

/-- ⋆⋆ = id on every (5, 1) pattern: 32 patterns × 5 indices. -/
theorem hodge_sq_pattern_5_1 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 1),
      hodgeStar 5 4 1 (hodgeStar 5 1 4 (pattern51 b0 b1 b2 b3 b4)) i
        = pattern51 b0 b1 b2 b3 b4 i := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 1, ⋆⋆σ = σ. -/
theorem hodge_sq_prop_5_1 (σ : Cochain 5 1)
    (i : Fin (binom 5 1)) :
    hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i := by
  rw [UniversalProp51.pattern_eq σ]
  exact hodge_sq_pattern_5_1 _ _ _ _ _ i

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 1). -/
theorem hodge_involution_capstone :
    ∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
      hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i :=
  hodge_sq_prop_5_1

end E213.Math.Cohomology.HodgeProp
