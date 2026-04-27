import E213.Research.Real213CutMulComm
import E213.Research.Real213CutSumComm

/-!
# Research.Real213CutMulOne: cutMul (1)(1) = constCut 1 1 (general theorem)

via iff existential characterization + Nat arithmetic on bounds.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

private theorem bool_eq_of_iff_true_v3 (a b : Bool)
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **cutMul (1)(1) = constCut 1 1**: 1 * 1 = 1 as cut function. -/
theorem cutMul_one_one : cutMul (constCut 1 1) (constCut 1 1) = constCut 1 1 := by
  funext m k
  apply bool_eq_of_iff_true_v3
  show cutMulOuter (constCut 1 1) (constCut 1 1) k m
        ((m+1)*(k+1)) ((m+1)*(k+1)) = true
       ↔ constCut 1 1 m k = true
  rw [cutMulOuter_eq_true_iff]
  show (∃ m1, m1 ≤ (m+1)*(k+1) ∧ ∃ m2, m2 ≤ (m+1)*(k+1) ∧
         constCut 1 1 m1 k = true ∧ constCut 1 1 m2 k = true ∧ m1 * m2 ≤ m * k)
       ↔ constCut 1 1 m k = true
  constructor
  · rintro ⟨m1, _, m2, _, hcx, hcy, hmul⟩
    have h_m1 : k ≤ m1 := by
      have : 1*k ≤ 1*m1 := of_decide_eq_true hcx
      rwa [Nat.one_mul, Nat.one_mul] at this
    have h_m2 : k ≤ m2 := by
      have : 1*k ≤ 1*m2 := of_decide_eq_true hcy
      rwa [Nat.one_mul, Nat.one_mul] at this
    show decide (1*k ≤ 1*m) = true
    rw [Nat.one_mul, Nat.one_mul]
    apply decide_eq_true
    have hk_sq_le : k * k ≤ m * k :=
      Nat.le_trans (Nat.mul_le_mul h_m1 h_m2) hmul
    cases k with
    | zero => exact Nat.zero_le _
    | succ j =>
      have : (j+1) * (j+1) ≤ (j+1) * m := by
        rw [Nat.mul_comm m (j+1)] at hk_sq_le; exact hk_sq_le
      exact Nat.le_of_mul_le_mul_left this (Nat.succ_pos _)
  · intro h_le
    have h_km : k ≤ m := by
      have : 1*k ≤ 1*m := of_decide_eq_true h_le
      rwa [Nat.one_mul, Nat.one_mul] at this
    have hk_bound : k ≤ (m+1)*(k+1) :=
      Nat.le_trans (Nat.le_succ k)
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    refine ⟨k, hk_bound, k, hk_bound, ?_, ?_, ?_⟩
    · show decide (1*k ≤ 1*k) = true
      exact decide_eq_true (Nat.le_refl _)
    · show decide (1*k ≤ 1*k) = true
      exact decide_eq_true (Nat.le_refl _)
    · exact Nat.mul_le_mul_right k h_km

end E213.Research.Real213CutSum
