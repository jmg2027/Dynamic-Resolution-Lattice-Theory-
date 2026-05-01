import E213.Math.Cohomology.Universal.Core

/-!
# Universal δ²=0 — Prop-level lift at (n, 0)

Cochain n 0 = Fin 1 → Bool has only 2 functions. Case-split on
`σ ⟨0, _⟩` + funext gives Prop-level ∀ σ.

Pulls in funext (≤ {propext, Quot.sound}).
-/

namespace E213.Math.Cohomology.Universal.Core.Prop

open E213.Physics.Simplex (binom)

/-- Helper: δ²(zero 3 0) = 0 (∀ form). -/
theorem aux_zero_3_0 :
    ∀ i : Fin (binom 3 2), delta (delta (Cochain.zero 3 0)) i = false := by
  decide

/-- Helper: δ²(true at (3, 0)) = 0 (∀ form). -/
theorem aux_true_3_0 :
    ∀ i : Fin (binom 3 2),
      delta (delta (fun _ : Fin (binom 3 0) => true)) i = false := by decide

/-- Helper: δ²(zero 4 0) = 0 (∀ form). -/
theorem aux_zero_4_0 :
    ∀ i : Fin (binom 4 2), delta (delta (Cochain.zero 4 0)) i = false := by
  decide

/-- Helper: δ²(true at (4, 0)) = 0. -/
theorem aux_true_4_0 :
    ∀ i : Fin (binom 4 2),
      delta (delta (fun _ : Fin (binom 4 0) => true)) i = false := by decide

/-- Helper: δ²(zero 5 0) = 0 (∀ form). -/
theorem aux_zero_5_0 :
    ∀ i : Fin (binom 5 2), delta (delta (Cochain.zero 5 0)) i = false := by
  decide

/-- Helper: δ²(true at (5, 0)) = 0. -/
theorem aux_true_5_0 :
    ∀ i : Fin (binom 5 2),
      delta (delta (fun _ : Fin (binom 5 0) => true)) i = false := by decide

/-- ★ Prop-level ∀ σ : Cochain 5 0, δ²σ = 0. -/
theorem dsq_zero_prop_5_0 (σ : Cochain 5 0)
    (i : Fin (binom 5 2)) : delta (delta σ) i = false := by
  match hσ : σ ⟨0, by decide⟩ with
  | true =>
    have heq : σ = (fun _ => true) := by
      funext k; match k with | ⟨0, _⟩ => exact hσ
    rw [heq]; exact aux_true_5_0 i
  | false =>
    have heq : σ = Cochain.zero 5 0 := by
      funext k; match k with | ⟨0, _⟩ => exact hσ
    rw [heq]; exact aux_zero_5_0 i

/-- ★ Prop-level ∀ σ : Cochain 3 0, δ²σ = 0. -/
theorem dsq_zero_prop_3_0 (σ : Cochain 3 0)
    (i : Fin (binom 3 2)) : delta (delta σ) i = false := by
  match hσ : σ ⟨0, by decide⟩ with
  | true =>
    have heq : σ = (fun _ => true) := by
      funext k; match k with | ⟨0, _⟩ => exact hσ
    rw [heq]; exact aux_true_3_0 i
  | false =>
    have heq : σ = Cochain.zero 3 0 := by
      funext k; match k with | ⟨0, _⟩ => exact hσ
    rw [heq]; exact aux_zero_3_0 i

/-- ★★★ Prop-level Universal δ²=0 at (n, 0) for n ∈ {3, 5}. -/
theorem dsq_zero_prop_n0_capstone :
    (∀ σ : Cochain 3 0, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 0, ∀ i, delta (delta σ) i = false) :=
  ⟨dsq_zero_prop_3_0, dsq_zero_prop_5_0⟩

end E213.Math.Cohomology.Universal.Core.Prop
