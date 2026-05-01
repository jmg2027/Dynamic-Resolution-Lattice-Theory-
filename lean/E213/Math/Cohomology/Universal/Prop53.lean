import E213.Math.Cohomology.Universal.Core.Prop52

/-!
# Universal δ²=0 Prop-lift at (5, 3) — Δ⁴ 3-cochain (top-stratum)

Cochain 5 3 = Fin (binom 5 3) → Bool = Fin 10 → Bool, 2¹⁰ = 1024
functions.  δ² goes 3 → 4 → 5 with codomain Fin (binom 5 5) = Fin 1
(single index).  1024 × 1 = 1024 evals.

Closes the (5, k) Universal chain at top stratum.  Together with
UniversalProp51 (5,1) and UniversalProp52 (5,2), this completes
δ²=0 over all interior strata of Δ⁴.
-/

namespace E213.Math.Cohomology.Universal.Prop53

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 5 3 parametrized by 10 Bool values. -/
def pattern (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Cochain 5 3 :=
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

/-- Any σ : Cochain 5 3 equals its pattern. -/
theorem pattern_eq (σ : Cochain 5 3) :
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
/-- δ²=0 on every pattern: 1024 Bool 10-tuples × 1 index. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 5),
        delta (delta (pattern b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 3, δ²σ = 0.
    Δ⁴ top-stratum Universal δ²=0. -/
theorem dsq_zero_prop_5_3 (σ : Cochain 5 3)
    (i : Fin (binom 5 5)) : delta (delta σ) i = false := by
  rw [pattern_eq σ]
  exact dsq_pattern _ _ _ _ _ _ _ _ _ _ i

end E213.Math.Cohomology.Universal.Prop53
