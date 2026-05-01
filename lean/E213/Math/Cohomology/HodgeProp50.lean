import E213.Math.Cohomology.HodgeStar

/-!
# ⋆⋆ = id Prop-lift at (5, 0) — Δ⁴ scalar cochain (trivial stratum)

Cochain 5 0 = Fin (binom 5 0) → Bool = Fin 1 → Bool, only 2
functions (constant true, constant false).  ⋆⋆ identity is
trivial via direct enumeration.

Closes the bottom stratum of the Hodge involution chain
(5, 0) → (5, 1) → (5, 2) → (5, 3) → (5, 4) over Δ⁴.
-/

namespace E213.Math.Cohomology.HodgeProp50

open E213.Physics.Simplex (binom)

/-- Cochain 5 0 parametrized by 1 Bool value. -/
def pattern (b0 : Bool) : Cochain 5 0 :=
  fun _ => b0

/-- Any σ : Cochain 5 0 equals its pattern. -/
theorem pattern_eq (σ : Cochain 5 0) :
    σ = pattern (σ ⟨0, by decide⟩) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl

/-- ⋆⋆ = id on every (5, 0) pattern (only 2 patterns). -/
theorem hodge_sq_pattern_5_0 :
    ∀ b0 : Bool, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 (pattern b0)) i = pattern b0 i := by
  decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 0, ⋆⋆σ = σ. -/
theorem hodge_sq_prop_5_0 (σ : Cochain 5 0)
    (i : Fin (binom 5 0)) :
    hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i := by
  rw [pattern_eq σ]
  exact hodge_sq_pattern_5_0 _ i

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 0). -/
theorem hodge_involution_capstone_5_0 :
    ∀ σ : Cochain 5 0, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i :=
  hodge_sq_prop_5_0

end E213.Math.Cohomology.HodgeProp50
