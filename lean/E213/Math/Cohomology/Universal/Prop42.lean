import E213.Math.Cohomology.Universal.Core.Prop41

/-!
# Universal δ²=0 Prop-lift at (4, 2) — Δ³ edge cochain

Cochain 4 2 = Fin 6 → Bool, 2⁶ = 64 functions.  Pattern via
6 Bool values.  δ² goes 2 → 3 → 4, codomain Fin (binom 4 4)
= Fin 1.  64 × 1 = 64 evals.
-/

namespace E213.Math.Cohomology.Universal.Core.Prop42

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 4 2 parametrized by 6 Bool values. -/
def pattern (b0 b1 b2 b3 b4 b5 : Bool) : Cochain 4 2 := fun i =>
  match i with
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5

/-- Any σ : Cochain 4 2 equals its pattern. -/
theorem pattern_eq (σ : Cochain 4 2) :
    σ = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩) := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

/-- δ²=0 on every (4, 2) pattern: 64 patterns × 1 index. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ i : Fin (binom 4 4),
      delta (delta (pattern b0 b1 b2 b3 b4 b5)) i = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 4 2, δ²σ = 0. -/
theorem dsq_zero_prop_4_2 (σ : Cochain 4 2)
    (i : Fin (binom 4 4)) : delta (delta σ) i = false := by
  rw [pattern_eq σ]
  exact dsq_pattern _ _ _ _ _ _ i

end E213.Math.Cohomology.Universal.Core.Prop42
