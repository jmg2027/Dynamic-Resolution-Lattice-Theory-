import E213.Math.Cohomology.Universal.Prop31

/-!
# Universal δ²=0 Prop-lift at (5, 1) — Δ⁴ vertex cochain case

Cochain 5 1 = Fin 5 → Bool, 2⁵ = 32 functions.  Pattern
parametrization with 5 Bool values gives full enumeration.

This is the **Δ⁴ vertex cochain** Universal δ²=0 — the case
most directly relevant to physics (vertex functions on the
5-vertex atomic substrate).
-/

namespace E213.Math.Cohomology.Universal.Prop51

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 5 1 parametrized by 5 Bool values. -/
def pattern (b0 b1 b2 b3 b4 : Bool) : Cochain 5 1 := fun i =>
  match i with
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4

/-- Any σ : Cochain 5 1 equals its pattern. -/
theorem pattern_eq (σ : Cochain 5 1) :
    σ = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                (σ ⟨4, by decide⟩) := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl

/-- δ²=0 on every pattern: 32 Bool quintuples × 10 indices. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 3),
      delta (delta (pattern b0 b1 b2 b3 b4)) i = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 1, δ²σ = 0.
    THIS IS THE Δ⁴ vertex cochain Universal δ²=0. -/
theorem dsq_zero_prop_5_1 (σ : Cochain 5 1)
    (i : Fin (binom 5 3)) : delta (delta σ) i = false := by
  rw [pattern_eq σ]
  exact dsq_pattern _ _ _ _ _ i

/-- ★★★ Universal δ²=0 Prop-lift at (5, 1) — Δ⁴ vertex case. -/
theorem prop_lift_5_1_capstone :
    ∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 3),
      delta (delta σ) i = false :=
  dsq_zero_prop_5_1

end E213.Math.Cohomology.Universal.Prop51
