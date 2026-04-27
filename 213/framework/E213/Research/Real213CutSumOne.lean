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
      have h_4k_2m : 2*(2*k) ≤ 2*m := Nat.mul_le_mul_left 2 h_2k_le_m
      omega

/-- **cutSum (0)(constCut a b) = constCut a b** (zero left identity). -/
theorem cutSum_zero_const (a b : Nat) :
    cutSum (constCut 0 1) (constCut a b) = constCut a b := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut 0 1) (constCut a b) k (2*m) (2*m) = true
       ↔ constCut a b m k = true
  rw [cutSumAux_eq_true_iff]
  constructor
  · rintro ⟨i, _, _, hci2⟩
    have h0 : a * (2*k) ≤ b * (2*m - i) := of_decide_eq_true hci2
    have h_2bm : b * (2*m - i) ≤ b * (2*m) :=
      Nat.mul_le_mul_left b (Nat.sub_le _ _)
    have h_2ak_2bm : a * (2*k) ≤ b * (2*m) := Nat.le_trans h0 h_2bm
    have e1 : a * (2*k) = 2 * (a*k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
    have e2 : b * (2*m) = 2 * (b*m) := by
      rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
    rw [e1, e2] at h_2ak_2bm
    show decide (a*k ≤ b*m) = true
    exact decide_eq_true (Nat.le_of_mul_le_mul_left h_2ak_2bm (by decide : 0 < 2))
  · intro h
    have h_ak : a*k ≤ b*m := of_decide_eq_true h
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · show decide (0 * (2*k) ≤ 1 * 0) = true
      exact decide_eq_true (by rw [Nat.zero_mul]; exact Nat.zero_le _)
    · show decide (a * (2*k) ≤ b * (2*m - 0)) = true
      rw [Nat.sub_zero]
      apply decide_eq_true
      have e1 : a * (2*k) = 2 * (a*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
      have e2 : b * (2*m) = 2 * (b*m) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
      rw [e1, e2]
      exact Nat.mul_le_mul_left 2 h_ak

/-- **cutSum (constCut a b) (constCut 0 1) = constCut a b** (right zero identity).
    Via cutSum_comm + cutSum_zero_const. -/
theorem cutSum_const_zero (a b : Nat) :
    cutSum (constCut a b) (constCut 0 1) = constCut a b := by
  funext m k
  rw [cutSum_comm (constCut a b) (constCut 0 1) m k]
  exact congrFun (congrFun (cutSum_zero_const a b) m) k

/-- **cutSum (1/2) (1/2) = constCut 1 1**: 1/2 + 1/2 = 1. -/
theorem cutSum_half_half :
    cutSum (constCut 1 2) (constCut 1 2) = constCut 1 1 := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut 1 2) (constCut 1 2) k (2*m) (2*m) = true
       ↔ constCut 1 1 m k = true
  rw [cutSumAux_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_2k_2i : 2*k ≤ 2*i := by
      have : 1*(2*k) ≤ 2*i := of_decide_eq_true hci
      rwa [Nat.one_mul] at this
    have h_2k_2mi : 2*k ≤ 2*(2*m - i) := by
      have : 1*(2*k) ≤ 2*(2*m - i) := of_decide_eq_true hcsi
      rwa [Nat.one_mul] at this
    have h_k_i : k ≤ i := Nat.le_of_mul_le_mul_left h_2k_2i (by decide : 0 < 2)
    have h_k_mi : k ≤ 2*m - i := Nat.le_of_mul_le_mul_left h_2k_2mi (by decide : 0 < 2)
    show decide (1*k ≤ 1*m) = true
    rw [Nat.one_mul, Nat.one_mul]
    apply decide_eq_true
    omega
  · intro h
    have h_km : 1*k ≤ 1*m := of_decide_eq_true h
    rw [Nat.one_mul, Nat.one_mul] at h_km
    refine ⟨k, ?_, ?_, ?_⟩
    · omega
    · show decide (1*(2*k) ≤ 2*k) = true
      rw [Nat.one_mul]
      exact decide_eq_true (Nat.le_refl _)
    · show decide (1*(2*k) ≤ 2*(2*m - k)) = true
      rw [Nat.one_mul]
      apply decide_eq_true
      omega

/-- **cutSum (1/3) (1/3) = constCut 2 3**: 1/3 + 1/3 = 2/3. -/
theorem cutSum_third_third :
    cutSum (constCut 1 3) (constCut 1 3) = constCut 2 3 := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut 1 3) (constCut 1 3) k (2*m) (2*m) = true
       ↔ constCut 2 3 m k = true
  rw [cutSumAux_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_2k_3i : 2*k ≤ 3*i := by
      have : 1*(2*k) ≤ 3*i := of_decide_eq_true hci
      rwa [Nat.one_mul] at this
    have h_2k_3mi : 2*k ≤ 3*(2*m - i) := by
      have : 1*(2*k) ≤ 3*(2*m - i) := of_decide_eq_true hcsi
      rwa [Nat.one_mul] at this
    show decide (2*k ≤ 3*m) = true
    apply decide_eq_true
    have h_add : (2*m - i) + i = 2*m := Nat.sub_add_cancel hi
    have h_sum : 3*i + 3*(2*m - i) = 6*m := by
      rw [Nat.add_comm]
      rw [← Nat.mul_add]
      rw [h_add]
      omega
    omega
  · intro h
    have h_2k_3m : 2*k ≤ 3*m := of_decide_eq_true h
    refine ⟨m, ?_, ?_, ?_⟩
    · -- m ≤ 2m
      omega
    · show decide (1*(2*k) ≤ 3*m) = true
      rw [Nat.one_mul]
      exact decide_eq_true h_2k_3m
    · show decide (1*(2*k) ≤ 3*(2*m - m)) = true
      rw [Nat.one_mul]
      have : 2*m - m = m := by omega
      rw [this]
      exact decide_eq_true h_2k_3m

end E213.Research.Real213CutSum
