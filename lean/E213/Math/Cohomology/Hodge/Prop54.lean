import E213.Math.Cohomology.Hodge.Star

/-!
# ⋆⋆ = id Prop-lift at (5, 4) — Δ⁴ 4-cochain (Hodge dual of (5, 1))

Cochain 5 4 = Fin (binom 5 4) → Bool = Fin 5 → Bool, 32 functions.
By Hodge duality, the structure is identical to (5, 1):
binom 5 4 = binom 5 1 = 5.  ⋆⋆ : C⁴ → C⁴ is computed via
⋆ : C⁴ → C¹ → ⋆ : C¹ → C⁴.

Closes the top-1 stratum of the Hodge involution chain.
32 patterns × 5 indices = 160 evaluations.
-/

namespace E213.Math.Cohomology.Hodge.Prop54

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 5 4 parametrized by 5 Bool values. -/
def pattern (b0 b1 b2 b3 b4 : Bool) : Cochain 5 4 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => b0
    | ⟨1, _⟩ => b1
    | ⟨2, _⟩ => b2
    | ⟨3, _⟩ => b3
    | ⟨4, _⟩ => b4

/-- Any σ : Cochain 5 4 equals its pattern. -/
theorem pattern_eq (σ : Cochain 5 4) :
    σ = pattern
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
      (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
      (σ ⟨4, by decide⟩) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl

/-- ⋆⋆ = id on every (5, 4) pattern: 32 patterns × 5 indices. -/
theorem hodge_sq_pattern_5_4 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 (hodgeStar 5 4 1 (pattern b0 b1 b2 b3 b4)) i
        = pattern b0 b1 b2 b3 b4 i := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 4, ⋆⋆σ = σ. -/
theorem hodge_sq_prop_5_4 (σ : Cochain 5 4)
    (i : Fin (binom 5 4)) :
    hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i := by
  rw [pattern_eq σ]
  exact hodge_sq_pattern_5_4 _ _ _ _ _ i

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 4). -/
theorem hodge_involution_capstone_5_4 :
    ∀ σ : Cochain 5 4, ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i :=
  hodge_sq_prop_5_4

end E213.Math.Cohomology.Hodge.Prop54
