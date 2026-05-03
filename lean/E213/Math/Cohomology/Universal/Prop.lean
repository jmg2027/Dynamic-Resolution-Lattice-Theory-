import E213.Kernel.Tactic.Nat213
import E213.Math.Cohomology.Delta.Pointwise
import E213.Math.Cohomology.Universal.Core

/-!
# Universal δ²=0 — Prop-level lift at (n, 0)

Cochain n 0 = Fin 1 → Bool has only 2 functions. Case-split on
`σ ⟨0, _⟩` + funext gives Prop-level ∀ σ.

Pulls in funext (≤ {propext, Quot.sound}).
-/

namespace E213.Math.Cohomology.Universal.Prop

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)

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

/-- Pointwise equality at n=3: σ with σ⟨0⟩ = true equals constant-true. -/
private theorem cochain_30_true_at (σ : Cochain 3 0)
    (hσ : σ ⟨0, by decide⟩ = true) :
    ∀ j, σ j = (fun _ : Fin (binom 3 0) => true) j := by
  intro j
  obtain ⟨v, hv⟩ := j
  have h_v0 : v = 0 := by
    match v, hv with
    | 0, _ => rfl
    | n+1, h => exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero n)
  subst h_v0
  exact hσ

private theorem cochain_30_false_at (σ : Cochain 3 0)
    (hσ : σ ⟨0, by decide⟩ = false) :
    ∀ j, σ j = Cochain.zero 3 0 j := by
  intro j
  obtain ⟨v, hv⟩ := j
  have h_v0 : v = 0 := by
    match v, hv with
    | 0, _ => rfl
    | n+1, h => exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero n)
  subst h_v0
  exact hσ

private theorem cochain_50_true_at (σ : Cochain 5 0)
    (hσ : σ ⟨0, by decide⟩ = true) :
    ∀ j, σ j = (fun _ : Fin (binom 5 0) => true) j := by
  intro j
  obtain ⟨v, hv⟩ := j
  have h_v0 : v = 0 := by
    match v, hv with
    | 0, _ => rfl
    | n+1, h => exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero n)
  subst h_v0
  exact hσ

private theorem cochain_50_false_at (σ : Cochain 5 0)
    (hσ : σ ⟨0, by decide⟩ = false) :
    ∀ j, σ j = Cochain.zero 5 0 j := by
  intro j
  obtain ⟨v, hv⟩ := j
  have h_v0 : v = 0 := by
    match v, hv with
    | 0, _ => rfl
    | n+1, h => exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero n)
  subst h_v0
  exact hσ

/-- ★ Prop-level ∀ σ : Cochain 5 0, δ²σ = 0.  PURE via twice-applied
    `delta_pointwise_eq`. -/
theorem dsq_zero_prop_5_0 (σ : Cochain 5 0)
    (i : Fin (binom 5 2)) : delta (delta σ) i = false := by
  match hσ : σ ⟨0, by decide⟩ with
  | true =>
    have h_pt := cochain_50_true_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (fun _ : Fin (binom 5 0) => true)) i :=
      delta_pointwise_eq (delta σ) (delta _)
        (fun j => delta_pointwise_eq σ _ h_pt j) i
    rw [h_outer]
    exact aux_true_5_0 i
  | false =>
    have h_pt := cochain_50_false_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (Cochain.zero 5 0)) i :=
      delta_pointwise_eq (delta σ) (delta _)
        (fun j => delta_pointwise_eq σ _ h_pt j) i
    rw [h_outer]
    exact aux_zero_5_0 i

/-- ★ Prop-level ∀ σ : Cochain 3 0, δ²σ = 0.  PURE. -/
theorem dsq_zero_prop_3_0 (σ : Cochain 3 0)
    (i : Fin (binom 3 2)) : delta (delta σ) i = false := by
  match hσ : σ ⟨0, by decide⟩ with
  | true =>
    have h_pt := cochain_30_true_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (fun _ : Fin (binom 3 0) => true)) i :=
      delta_pointwise_eq (delta σ) (delta _)
        (fun j => delta_pointwise_eq σ _ h_pt j) i
    rw [h_outer]
    exact aux_true_3_0 i
  | false =>
    have h_pt := cochain_30_false_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (Cochain.zero 3 0)) i :=
      delta_pointwise_eq (delta σ) (delta _)
        (fun j => delta_pointwise_eq σ _ h_pt j) i
    rw [h_outer]
    exact aux_zero_3_0 i

/-- ★★★ Prop-level Universal δ²=0 at (n, 0) for n ∈ {3, 5}. -/
theorem dsq_zero_prop_n0_capstone :
    (∀ σ : Cochain 3 0, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 0, ∀ i, delta (delta σ) i = false) :=
  ⟨dsq_zero_prop_3_0, dsq_zero_prop_5_0⟩

end E213.Math.Cohomology.Universal.Prop
