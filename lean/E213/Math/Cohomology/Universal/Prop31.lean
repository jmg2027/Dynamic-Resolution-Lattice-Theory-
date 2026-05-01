import E213.Math.Cohomology.Universal.Core.Prop

/-!
# Universal δ²=0 Prop-lift at (3, 1)

User: hard deferred items resolution.  Extend Universal δ²=0
Prop-lift from (n, 0) to (n, 1) at concrete n.

For (3, 1): Cochain 3 1 = Fin 3 → Bool, 2³ = 8 functions.
Approach: parametrize via 3 Bool values, prove ∀ b0 b1 b2,
δ²(pattern b0 b1 b2) = 0 by decide (8-case enumeration).

Then any σ : Cochain 3 1 = pattern (σ⟨0⟩, σ⟨1⟩, σ⟨2⟩) by
funext, lift via this representation.
-/

namespace E213.Math.Cohomology.Universal.Prop31

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 3 1 parametrized by 3 Bool values. -/
def pattern (b0 b1 b2 : Bool) : Cochain 3 1 := fun i =>
  match i with
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2

/-- Any σ : Cochain 3 1 equals its pattern. -/
theorem pattern_eq (σ : Cochain 3 1) :
    σ = pattern (σ ⟨0, by decide⟩)
                (σ ⟨1, by decide⟩)
                (σ ⟨2, by decide⟩) := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- δ²=0 on every pattern, all 8 Bool triples × 1 index. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 : Bool, ∀ i : Fin (binom 3 3),
      delta (delta (pattern b0 b1 b2)) i = false := by decide

/-- ★ Prop-level ∀ σ : Cochain 3 1, δ²σ = 0. -/
theorem dsq_zero_prop_3_1 (σ : Cochain 3 1)
    (i : Fin (binom 3 3)) : delta (delta σ) i = false := by
  rw [pattern_eq σ]
  exact dsq_pattern _ _ _ i

/-- ★★★ Capstone: Prop-level Universal δ²=0 extends to (3, 1). -/
theorem prop_lift_capstone :
    (∀ σ : Cochain 3 0, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 0, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 3 1, ∀ i, delta (delta σ) i = false) :=
  ⟨E213.Math.Cohomology.Universal.Core.Prop.dsq_zero_prop_3_0,
   E213.Math.Cohomology.Universal.Core.Prop.dsq_zero_prop_5_0,
   dsq_zero_prop_3_1⟩

end E213.Math.Cohomology.Universal.Prop31
