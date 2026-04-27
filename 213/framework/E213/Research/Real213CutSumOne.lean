import E213.Research.Real213CutSumComm
import E213.Research.Real213CutMulOne

/-!
# Research.Real213CutSumOne: cutSum (1)(1) = constCut 2 1 (general theorem)
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

private theorem bool_eq_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **cutSum (1)(1) = constCut 2 1**: 1 + 1 = 2 as cut function. -/
theorem cutSum_one_one :
    cutSum (constCut 1 1) (constCut 1 1) = constCut 2 1 := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut 1 1) (constCut 1 1) k (2*m) (2*m) = true
       ↔ constCut 2 1 m k = true
  rw [cutSumAux_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_2k_le_i : 2*k ≤ i := by
      have : 1*(2*k) ≤ 1*i := of_decide_eq_true hci
      rwa [Nat.one_mul, Nat.one_mul] at this
    have h_2k_le_2mi : 2*k ≤ 2*m - i := by
      have : 1*(2*k) ≤ 1*(2*m-i) := of_decide_eq_true hcsi
      rwa [Nat.one_mul, Nat.one_mul] at this
    have h_4k_le_2m : 2*k + 2*k ≤ 2*m := by
      calc 2*k + 2*k ≤ i + (2*m - i) := Nat.add_le_add h_2k_le_i h_2k_le_2mi
        _ = 2*m := Nat.add_sub_of_le hi
    show decide (2*k ≤ 1*m) = true
    rw [Nat.one_mul]
    apply decide_eq_true
    omega
  · intro h
    have h_2k_le_m : 2*k ≤ m := by
      have : 2*k ≤ 1*m := of_decide_eq_true h
      rwa [Nat.one_mul] at this
    refine ⟨2*k, ?_, ?_, ?_⟩
    · -- 2k ≤ 2m (from 2k ≤ m)
      exact Nat.le_trans h_2k_le_m (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
    · show decide (1*(2*k) ≤ 1*(2*k)) = true
      exact decide_eq_true (Nat.le_refl _)
    · show decide (1*(2*k) ≤ 1*(2*m - 2*k)) = true
      rw [Nat.one_mul, Nat.one_mul]
      apply decide_eq_true
      -- Goal: 2k ≤ 2m - 2k.  From 2k ≤ m, we have 4k ≤ 2m, so 2k ≤ 2m - 2k.
      have h_4k_2m : 2*(2*k) ≤ 2*m := Nat.mul_le_mul_left 2 h_2k_le_m
      omega

end E213.Research.Real213CutSum
