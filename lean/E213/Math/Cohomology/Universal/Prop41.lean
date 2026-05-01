import E213.Math.Cohomology.Universal.Core.Prop31

/-!
# Universal δ²=0 Prop-lift at (4, 1) — Δ³ vertex cochain

Cochain 4 1 = Fin 4 → Bool, 2⁴ = 16 functions.  Pattern parametrize
via 4 Bool values.

This is the Δ³ vertex cochain Universal δ²=0 — bridges the (3, 1)
and (5, 1) cases.
-/

namespace E213.Math.Cohomology.Universal.Prop41

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 4 1 parametrized by 4 Bool values. -/
def pattern (b0 b1 b2 b3 : Bool) : Cochain 4 1 := fun i =>
  match i with
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3

/-- Any σ : Cochain 4 1 equals its pattern. -/
theorem pattern_eq (σ : Cochain 4 1) :
    σ = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩) := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

/-- δ²=0 on every (4, 1) pattern: 16 patterns × 4 indices. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 : Bool, ∀ i : Fin (binom 4 3),
      delta (delta (pattern b0 b1 b2 b3)) i = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 4 1, δ²σ = 0. -/
theorem dsq_zero_prop_4_1 (σ : Cochain 4 1)
    (i : Fin (binom 4 3)) : delta (delta σ) i = false := by
  rw [pattern_eq σ]
  exact dsq_pattern _ _ _ _ i

end E213.Math.Cohomology.Universal.Prop41
