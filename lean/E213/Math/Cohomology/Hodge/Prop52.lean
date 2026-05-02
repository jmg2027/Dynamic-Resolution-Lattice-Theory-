import E213.Math.Cohomology.Universal.Prop52

/-!
# ⋆⋆ = id Prop-lift at (5, 2) — Δ⁴ edge cochain involution

Cochain 5 2 = Fin 10 → Bool, 1024 patterns × 10 indices = 10240
hodge ⋆⋆ evaluations.  Together with HodgeProp (5,1), establishes
the involution on the two physically meaningful strata of Δ⁴:
vertex (5,1) and edge (5,2) cochains.
-/

namespace E213.Math.Cohomology.Hodge.Prop52

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 5 2 parametrized (re-exported from UniversalProp52). -/
abbrev pattern52 := UniversalProp52.pattern

set_option maxHeartbeats 8000000 in
/-- ⋆⋆ = id on every (5, 2) pattern: 1024 patterns × 10 indices. -/
theorem hodge_sq_pattern_5_2 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2
        (hodgeStar 5 2 3 (pattern52 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
        = pattern52 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 i := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 2, ⋆⋆σ = σ. -/
theorem hodge_sq_prop_5_2 (σ : Cochain 5 2)
    (i : Fin (binom 5 2)) :
    hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i := by
  rw [UniversalProp52.pattern_eq σ]
  exact hodge_sq_pattern_5_2 _ _ _ _ _ _ _ _ _ _ i

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 2). -/
theorem hodge_involution_capstone_5_2 :
    ∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i :=
  hodge_sq_prop_5_2

end E213.Math.Cohomology.Hodge.Prop52
