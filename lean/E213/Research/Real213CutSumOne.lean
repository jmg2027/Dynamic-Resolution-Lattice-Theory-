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

/-- **cutSum (a/2) (b/2) = (a+b)/2** for any a, b. -/
theorem cutSum_half_general (a b : Nat) :
    cutSum (constCut a 2) (constCut b 2) = constCut (a + b) 2 := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut a 2) (constCut b 2) k (2*m) (2*m) = true
       ↔ constCut (a + b) 2 m k = true
  rw [cutSumAux_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_2ak_2i : a*(2*k) ≤ 2*i := of_decide_eq_true hci
    have h_2bk_2mi : b*(2*k) ≤ 2*(2*m - i) := of_decide_eq_true hcsi
    show decide ((a+b)*k ≤ 2*m) = true
    apply decide_eq_true
    have h_add : i + (2*m - i) = 2*m := Nat.add_sub_of_le hi
    have h_e1 : a*(2*k) = 2*(a*k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
    have h_e2 : b*(2*k) = 2*(b*k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
    rw [h_e1] at h_2ak_2i
    rw [h_e2] at h_2bk_2mi
    have h_ak : a*k ≤ i := Nat.le_of_mul_le_mul_left h_2ak_2i (by decide : 0 < 2)
    have h_bk : b*k ≤ 2*m - i := Nat.le_of_mul_le_mul_left h_2bk_2mi (by decide : 0 < 2)
    have h_abk : a*k + b*k ≤ i + (2*m - i) := Nat.add_le_add h_ak h_bk
    rw [h_add] at h_abk
    rw [show a*k + b*k = (a+b)*k from (Nat.add_mul a b k).symm] at h_abk
    exact h_abk
  · intro h
    have h_abk_2m : (a+b)*k ≤ 2*m := of_decide_eq_true h
    have h_ak_le_2m : a*k ≤ 2*m := by
      have : a*k ≤ (a+b)*k := by
        rw [Nat.add_mul]; exact Nat.le_add_right _ _
      exact Nat.le_trans this h_abk_2m
    refine ⟨a*k, h_ak_le_2m, ?_, ?_⟩
    · show decide (a*(2*k) ≤ 2*(a*k)) = true
      apply decide_eq_true
      have : a*(2*k) = 2*(a*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
      rw [this]
      exact Nat.le_refl _
    · show decide (b*(2*k) ≤ 2*(2*m - a*k)) = true
      apply decide_eq_true
      have e1 : b*(2*k) = 2*(b*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
      rw [e1]
      have h_abk' : a*k + b*k ≤ 2*m := by
        rw [show a*k + b*k = (a+b)*k from (Nat.add_mul a b k).symm]
        exact h_abk_2m
      omega

/-- **cutSum (a/1) (b/2) = (2*a + b)/2** for any a, b. -/
theorem cutSum_int_half (a b : Nat) :
    cutSum (constCut a 1) (constCut b 2) = constCut (2*a + b) 2 := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut a 1) (constCut b 2) k (2*m) (2*m) = true
       ↔ constCut (2*a + b) 2 m k = true
  rw [cutSumAux_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_2ak_i : 2*(a*k) ≤ i := by
      have h1 : a*(2*k) ≤ 1*i := of_decide_eq_true hci
      have e : a*(2*k) = 2*(a*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
      rw [Nat.one_mul] at h1; rwa [e] at h1
    have h_2bk_2mi : b*(2*k) ≤ 2*(2*m - i) := of_decide_eq_true hcsi
    show decide ((2*a + b)*k ≤ 2*m) = true
    apply decide_eq_true
    have h_bk : b*k ≤ 2*m - i := by
      have e : b*(2*k) = 2*(b*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
      rw [e] at h_2bk_2mi
      exact Nat.le_of_mul_le_mul_left h_2bk_2mi (by decide : 0 < 2)
    have h_add : i + (2*m - i) = 2*m := Nat.add_sub_of_le hi
    have h_total : 2*(a*k) + b*k ≤ 2*m := by
      calc 2*(a*k) + b*k ≤ i + (2*m - i) := Nat.add_le_add h_2ak_i h_bk
        _ = 2*m := h_add
    have e_lhs : (2*a + b)*k = 2*(a*k) + b*k := by
      rw [Nat.add_mul, Nat.mul_assoc]
    rw [e_lhs]
    exact h_total
  · intro h
    have h_le : (2*a + b)*k ≤ 2*m := of_decide_eq_true h
    have h_total : 2*(a*k) + b*k ≤ 2*m := by
      have e : (2*a + b)*k = 2*(a*k) + b*k := by
        rw [Nat.add_mul, Nat.mul_assoc]
      rw [e] at h_le; exact h_le
    refine ⟨2*(a*k), ?_, ?_, ?_⟩
    · omega
    · show decide (a*(2*k) ≤ 1*(2*(a*k))) = true
      rw [Nat.one_mul]
      have : a*(2*k) = 2*(a*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
      rw [this]
      exact decide_eq_true (Nat.le_refl _)
    · show decide (b*(2*k) ≤ 2*(2*m - 2*(a*k))) = true
      apply decide_eq_true
      have e : b*(2*k) = 2*(b*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
      rw [e]
      omega

/-- **cutSum (a/2) (b/1) = (a + 2*b)/2**: half + int via comm. -/
theorem cutSum_half_int (a b : Nat) :
    cutSum (constCut a 2) (constCut b 1) = constCut (a + 2*b) 2 := by
  funext m k
  rw [cutSum_comm]
  have h := congrFun (congrFun (cutSum_int_half b a) m) k
  rw [h, Nat.add_comm (2*b) a]

/-- **cutSum (a/1) (b/1) = (a+b)/1** for integers. -/
theorem cutSum_int_int (a b : Nat) :
    cutSum (constCut a 1) (constCut b 1) = constCut (a + b) 1 := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut a 1) (constCut b 1) k (2*m) (2*m) = true
       ↔ constCut (a + b) 1 m k = true
  rw [cutSumAux_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_2ak_i : 2*(a*k) ≤ i := by
      have : a*(2*k) ≤ 1*i := of_decide_eq_true hci
      rw [Nat.one_mul] at this
      have e : a*(2*k) = 2*(a*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
      rwa [e] at this
    have h_2bk_2mi : 2*(b*k) ≤ 2*m - i := by
      have : b*(2*k) ≤ 1*(2*m - i) := of_decide_eq_true hcsi
      rw [Nat.one_mul] at this
      have e : b*(2*k) = 2*(b*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
      rwa [e] at this
    show decide ((a+b)*k ≤ 1*m) = true
    rw [Nat.one_mul]
    apply decide_eq_true
    have h_add : i + (2*m - i) = 2*m := Nat.add_sub_of_le hi
    have h_2abk_2m : 2*(a*k) + 2*(b*k) ≤ 2*m := by
      calc 2*(a*k) + 2*(b*k)
          ≤ i + (2*m - i) := Nat.add_le_add h_2ak_i h_2bk_2mi
        _ = 2*m := h_add
    have e : 2*(a*k) + 2*(b*k) = 2 * ((a+b)*k) := by
      rw [← Nat.mul_add, Nat.add_mul]
    rw [e] at h_2abk_2m
    exact Nat.le_of_mul_le_mul_left h_2abk_2m (by decide : 0 < 2)
  · intro h
    have h_abk_m : (a+b)*k ≤ 1*m := of_decide_eq_true h
    rw [Nat.one_mul] at h_abk_m
    refine ⟨2*(a*k), ?_, ?_, ?_⟩
    · -- 2ak ≤ 2m
      have : a*k ≤ (a+b)*k := by
        rw [Nat.add_mul]; exact Nat.le_add_right _ _
      have h_ak_m : a*k ≤ m := Nat.le_trans this h_abk_m
      omega
    · show decide (a*(2*k) ≤ 1*(2*(a*k))) = true
      rw [Nat.one_mul]
      have e : a*(2*k) = 2*(a*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a, Nat.mul_assoc]
      rw [e]
      exact decide_eq_true (Nat.le_refl _)
    · show decide (b*(2*k) ≤ 1*(2*m - 2*(a*k))) = true
      rw [Nat.one_mul]
      apply decide_eq_true
      have e : b*(2*k) = 2*(b*k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b, Nat.mul_assoc]
      rw [e]
      have h_abk' : a*k + b*k ≤ m := by
        rw [show a*k + b*k = (a+b)*k from (Nat.add_mul a b k).symm]
        exact h_abk_m
      omega

/-- **cutSum c c = 2c** for constant cut c = a/b. -/
theorem cutSum_self (a b : Nat) :
    cutSum (constCut a b) (constCut a b) = constCut (2*a) b := by
  funext m k
  apply bool_eq_iff
  show cutSumAux (constCut a b) (constCut a b) k (2*m) (2*m) = true
       ↔ constCut (2*a) b m k = true
  rw [cutSumAux_eq_true_iff]
  have e_a2k : a * (2*k) = 2 * (a*k) := by
    rw [Nat.mul_comm a (2*k), Nat.mul_assoc, Nat.mul_comm k a]
  have e_b2m : b * (2*m) = 2 * (b*m) := by
    rw [Nat.mul_comm b (2*m), Nat.mul_assoc, Nat.mul_comm m b]
  have e_2ak : (2*a)*k = 2*(a*k) := Nat.mul_assoc 2 a k
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_a2k_bi : a*(2*k) ≤ b*i := of_decide_eq_true hci
    have h_a2k_b2mi : a*(2*k) ≤ b*(2*m - i) := of_decide_eq_true hcsi
    show decide ((2*a)*k ≤ b*m) = true
    apply decide_eq_true
    have h_add : i + (2*m - i) = 2*m := Nat.add_sub_of_le hi
    have h_sum_2bm : b*i + b*(2*m - i) = b*(2*m) := by
      rw [← Nat.mul_add, h_add]
    have h_2_a2k : 2 * (a*(2*k)) ≤ b*(2*m) := by
      calc 2 * (a*(2*k)) = a*(2*k) + a*(2*k) := Nat.two_mul _
        _ ≤ b*i + b*(2*m - i) := Nat.add_le_add h_a2k_bi h_a2k_b2mi
        _ = b*(2*m) := h_sum_2bm
    rw [e_a2k, e_b2m] at h_2_a2k
    -- h_2_a2k : 2 * (2 * (a*k)) ≤ 2 * (b*m)
    have h_2ak_bm : 2 * (a*k) ≤ b*m :=
      Nat.le_of_mul_le_mul_left h_2_a2k (by decide : 0 < 2)
    rw [e_2ak]; exact h_2ak_bm
  · intro h
    have h_2ak_bm : (2*a)*k ≤ b*m := of_decide_eq_true h
    rw [e_2ak] at h_2ak_bm
    -- h_2ak_bm : 2*(a*k) ≤ b*m
    have h_a2k_bm : a*(2*k) ≤ b*m := by rw [e_a2k]; exact h_2ak_bm
    refine ⟨m, ?_, ?_, ?_⟩
    · omega
    · show decide (a*(2*k) ≤ b*m) = true
      exact decide_eq_true h_a2k_bm
    · show decide (a*(2*k) ≤ b*(2*m - m)) = true
      have : 2*m - m = m := by omega
      rw [this]
      exact decide_eq_true h_a2k_bm

end E213.Research.Real213CutSum
