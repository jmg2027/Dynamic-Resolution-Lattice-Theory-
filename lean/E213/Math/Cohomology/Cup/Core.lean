import E213.Math.Cohomology.BettiKernel

/-!
# Cohomology — cup product (Phase CD, file 1)

Alexander–Whitney cup product
    ⌣ : Cᵏ × Cˡ → Cᵏ⁺ˡ
    (α ⌣ β)(τ) = α(τ first k) · β(τ last l)
over a sorted (k+l)-subset τ.  In ℤ/2 (Bool) `·` is AND.
All three arities (n, k, l) explicit to avoid metavariables.
-/

namespace E213.Math.Cohomology.Cup.Core

open E213.Physics.Simplex.Counts (binom d NS NT)

/-- Cup product (Alexander–Whitney) at fixed (n, k, l). -/
def cup (n k l : Nat) (α : Cochain n k) (β : Cochain n l) :
    Cochain n (k + l) :=
  fun τ_idx =>
    let τ := kSubset n (k + l) τ_idx.val
    let front := τ.take k
    let back := τ.drop k
    let f_idx := subsetIdx n k front
    let b_idx := subsetIdx n l back
    if hf : f_idx < binom n k then
      if hb : b_idx < binom n l then
        α ⟨f_idx, hf⟩ && β ⟨b_idx, hb⟩
      else false
    else false

/-- Smoke: cup with zero left = zero. -/
theorem cup_zero_left_5_1_1 :
    ∀ i : Fin (binom 5 2),
      cup 5 1 1 (Cochain.zero 5 1) v0_5 i = false := by decide

/-- Smoke: cup with zero right = zero. -/
theorem cup_zero_right_5_1_1 :
    ∀ i : Fin (binom 5 2),
      cup 5 1 1 v0_5 (Cochain.zero 5 1) i = false := by decide

/-- v0 ⌣ v0 on edge [0,1]: front=[0], back=[1]; v0([0])=true,
    v0([1])=false; AND = false. -/
theorem cup_v0_v0_concrete :
    cup 5 1 1 v0_5 v0_5 ⟨0, by decide⟩ = false
    ∧ cup 5 1 1 v0_5 v0_5 ⟨1, by decide⟩ = false := by decide

/-- All-ones cochain at (5, 1). -/
def all_true_5_1 : Cochain 5 1 := fun _ => true

/-- All-ones ⌣ all-ones at edge [0,1] = true AND true = true. -/
theorem cup_all_true_5_1_at_edge0 :
    cup 5 1 1 all_true_5_1 all_true_5_1 ⟨0, by decide⟩ = true := by decide

/-- ★ Phase CD intermediate capstone (file 1) — cup well-defined
    and decide-checked; zero-on-either-side preserved. -/
theorem phase_CD_cup_smoke :
    (∀ i : Fin (binom 5 2),
       cup 5 1 1 (Cochain.zero 5 1) v0_5 i = false)
    ∧ (∀ i : Fin (binom 5 2),
         cup 5 1 1 v0_5 (Cochain.zero 5 1) i = false)
    ∧ (cup 5 1 1 all_true_5_1 all_true_5_1 ⟨0, by decide⟩ = true) :=
  ⟨cup_zero_left_5_1_1, cup_zero_right_5_1_1, cup_all_true_5_1_at_edge0⟩

end E213.Math.Cohomology.Cup.Core
