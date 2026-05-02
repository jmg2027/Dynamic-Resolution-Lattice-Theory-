import E213.Math.Cohomology.Universal.Prop51

/-!
# Universal δ²=0 Prop-lift at (5, 2) — Δ⁴ edge cochain case

Cochain 5 2 = Fin (binom 5 2) → Bool = Fin 10 → Bool,
2¹⁰ = 1024 functions.

This is the **Δ⁴ edge cochain** Universal δ²=0 — relevant to
α_em + Yang-Mills mass gap (1-cochain on K_{3,2}^{(2)} edges).
-/

namespace E213.Math.Cohomology.Universal.Prop52

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Cochain.Core (Cochain)

/-- Cochain 5 2 parametrized by 10 Bool values. -/
def pattern (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Cochain 5 2 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => b0
    | ⟨1, _⟩ => b1
    | ⟨2, _⟩ => b2
    | ⟨3, _⟩ => b3
    | ⟨4, _⟩ => b4
    | ⟨5, _⟩ => b5
    | ⟨6, _⟩ => b6
    | ⟨7, _⟩ => b7
    | ⟨8, _⟩ => b8
    | ⟨9, _⟩ => b9

/-- Any σ : Cochain 5 2 equals its pattern. -/
theorem pattern_eq (σ : Cochain 5 2) :
    σ = pattern
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
      (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
      (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (σ ⟨8, by decide⟩)
      (σ ⟨9, by decide⟩) := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl
  | ⟨9, _⟩ => rfl

set_option maxHeartbeats 8000000 in
/-- δ²=0 on every pattern: 1024 Bool 10-tuples × 5 indices. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 4),
        delta (delta (pattern b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 2, δ²σ = 0.
    Δ⁴ edge cochain Universal δ²=0 — α_em / YM relevant. -/
theorem dsq_zero_prop_5_2 (σ : Cochain 5 2)
    (i : Fin (binom 5 4)) : delta (delta σ) i = false := by
  rw [pattern_eq σ]
  exact dsq_pattern _ _ _ _ _ _ _ _ _ _ i

end E213.Math.Cohomology.Universal.Prop52
