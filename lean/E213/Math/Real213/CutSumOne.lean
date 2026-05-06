import E213.Kernel.Tactic.Nat213
import E213.Math.Real213.CutSumComm
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutPoset

import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
/-!
# CutSumOne: cutSum (1)(1) = constCut 2 1 (general theorem)
-/

namespace E213.Math.Real213.CutSumOne

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSum (cutSum cutSumAux)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutSumComm (cutSumAux_eq_true_iff cutSum_comm)
open E213.Math.Real213.CutPoset (cutEq)

private theorem bool_eq_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **cutSum (1)(1) = constCut 2 1**: 1 + 1 = 2 as cut function. -/
theorem cutSum_one_one :
    cutEq (cutSum (constCut 1 1) (constCut 1 1)) (constCut 2 1) := by
  intro m k
  apply bool_eq_iff
  show cutSumAux (constCut 1 1) (constCut 1 1) k (2*m) (2*m) = true
       ↔ constCut 2 1 m k = true
  constructor
  · intro hLHS
    have hExt :=
      (cutSumAux_eq_true_iff (constCut 1 1) (constCut 1 1) k (2*m) (2*m)).mp hLHS
    obtain ⟨i, hi, hci, hcsi⟩ := hExt
    have h_2k_le_i : 2*k ≤ i := by
      have : 1*(2*k) ≤ 1*i := of_decide_eq_true hci
      rwa [Nat.one_mul, Nat.one_mul] at this
    have h_2k_le_2mi : 2*k ≤ 2*m - i := by
      have : 1*(2*k) ≤ 1*(2*m-i) := of_decide_eq_true hcsi
      rwa [Nat.one_mul, Nat.one_mul] at this
    have h_4k_le_2m : 2*k + 2*k ≤ 2*m := by
      calc 2*k + 2*k ≤ i + (2*m - i) := Nat.add_le_add h_2k_le_i h_2k_le_2mi
        _ = 2*m := E213.Tactic.Nat213.add_sub_of_le hi
    show decide (2*k ≤ 1*m) = true
    rw [Nat.one_mul]
    apply decide_eq_true
    have h_doubled : 2*(2*k) ≤ 2*m := by
      rw [Nat.two_mul]; exact h_4k_le_2m
    exact Nat.le_of_mul_le_mul_left h_doubled (by decide : 0 < 2)
  · intro h
    have h_2k_le_m : 2*k ≤ m := by
      have : 2*k ≤ 1*m := of_decide_eq_true h
      rwa [Nat.one_mul] at this
    apply (cutSumAux_eq_true_iff (constCut 1 1) (constCut 1 1) k (2*m) (2*m)).mpr
    refine ⟨2*k, ?_, ?_, ?_⟩
    · exact Nat.le_trans h_2k_le_m (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
    · show decide (1*(2*k) ≤ 1*(2*k)) = true
      exact decide_eq_true (Nat.le_refl _)
    · show decide (1*(2*k) ≤ 1*(2*m - 2*k)) = true
      rw [Nat.one_mul, Nat.one_mul]
      apply decide_eq_true
      have h_4k_2m : 2*(2*k) ≤ 2*m := Nat.mul_le_mul_left 2 h_2k_le_m
      have h_sum : 2*k + 2*k ≤ 2*m := by
        rw [← Nat.two_mul]; exact h_4k_2m
      exact E213.Tactic.Nat213.le_sub_of_add_le h_sum

/-- **cutSum (0)(constCut a b) ≡ constCut a b** (cutEq, zero left identity, PURE). -/
theorem cutSum_zero_const (a b : Nat) :
    cutEq (cutSum (constCut 0 1) (constCut a b)) (constCut a b) := by
  intro m k
  apply bool_eq_iff
  show cutSumAux (constCut 0 1) (constCut a b) k (2*m) (2*m) = true
       ↔ constCut a b m k = true
  constructor
  · intro hLHS
    have hExt :=
      (cutSumAux_eq_true_iff (constCut 0 1) (constCut a b) k (2*m) (2*m)).mp hLHS
    obtain ⟨i, _, _, hci2⟩ := hExt
    have h0 : a * (2*k) ≤ b * (2*m - i) := of_decide_eq_true hci2
    have h_2bm : b * (2*m - i) ≤ b * (2*m) :=
      Nat.mul_le_mul_left b (Nat.sub_le _ _)
    have h_2ak_2bm : a * (2*k) ≤ b * (2*m) := Nat.le_trans h0 h_2bm
    have e1 : a * (2*k) = 2 * (a*k) := by
      rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
    have e2 : b * (2*m) = 2 * (b*m) := by
      rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
    rw [e1, e2] at h_2ak_2bm
    show decide (a*k ≤ b*m) = true
    exact decide_eq_true (Nat.le_of_mul_le_mul_left h_2ak_2bm (by decide : 0 < 2))
  · intro h
    have h_ak : a*k ≤ b*m := of_decide_eq_true h
    apply (cutSumAux_eq_true_iff (constCut 0 1) (constCut a b) k (2*m) (2*m)).mpr
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · show decide (0 * (2*k) ≤ 1 * 0) = true
      exact decide_eq_true (by rw [Nat.zero_mul]; exact Nat.zero_le _)
    · show decide (a * (2*k) ≤ b * (2*m - 0)) = true
      rw [Nat.sub_zero]
      apply decide_eq_true
      have e1 : a * (2*k) = 2 * (a*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
      have e2 : b * (2*m) = 2 * (b*m) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
      rw [e1, e2]
      exact Nat.mul_le_mul_left 2 h_ak

/-- **cutSum (constCut a b) (constCut 0 1) ≡ constCut a b**
    (cutEq, right zero identity, PURE).  Via cutSum_comm + cutSum_zero_const. -/
theorem cutSum_const_zero (a b : Nat) :
    cutEq (cutSum (constCut a b) (constCut 0 1)) (constCut a b) := by
  intro m k
  rw [cutSum_comm (constCut a b) (constCut 0 1) m k]
  exact cutSum_zero_const a b m k

/-- **cutSum (1/2) (1/2) = constCut 1 1** pointwise (∅-axiom).
    Avoids `funext`, `rw [iff]`. -/
theorem cutSum_half_half_at (m k : Nat) :
    cutSum (constCut 1 2) (constCut 1 2) m k = constCut 1 1 m k := by
  apply bool_eq_iff
  show cutSumAux (constCut 1 2) (constCut 1 2) k (2*m) (2*m) = true
       ↔ constCut 1 1 m k = true
  refine Iff.trans (cutSumAux_eq_true_iff _ _ _ _ _) ?_
  constructor
  · rintro ⟨i, hi, hci, hcsi⟩
    have h_2k_2i : 2*k ≤ 2*i := by
      have : 1*(2*k) ≤ 2*i := of_decide_eq_true hci
      rwa [Nat.one_mul] at this
    have h_2k_2mi : 2*k ≤ 2*(2*m - i) := by
      have : 1*(2*k) ≤ 2*(2*m - i) := of_decide_eq_true hcsi
      rwa [Nat.one_mul] at this
    have h_k_i : k ≤ i :=
      Nat.le_of_mul_le_mul_left h_2k_2i (Nat.zero_lt_succ 1)
    have h_k_mi : k ≤ 2*m - i :=
      Nat.le_of_mul_le_mul_left h_2k_2mi (Nat.zero_lt_succ 1)
    show decide (1*k ≤ 1*m) = true
    rw [Nat.one_mul, Nat.one_mul]
    apply decide_eq_true
    -- k+k ≤ i + (2m - i) = 2m, so 2k ≤ 2m, so k ≤ m
    have h_kk : k + k ≤ i + (2*m - i) := Nat.add_le_add h_k_i h_k_mi
    rw [E213.Tactic.Nat213.add_sub_of_le hi] at h_kk
    have h_2k_2m : 2*k ≤ 2*m := by
      rw [Nat.two_mul]; exact h_kk
    exact Nat.le_of_mul_le_mul_left h_2k_2m (Nat.zero_lt_succ 1)
  · intro h
    have h_km : 1*k ≤ 1*m := of_decide_eq_true h
    rw [Nat.one_mul, Nat.one_mul] at h_km
    refine ⟨k, ?_, ?_, ?_⟩
    · exact Nat.le_trans h_km (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ 1))
    · show decide (1*(2*k) ≤ 2*k) = true
      rw [Nat.one_mul]
      exact decide_eq_true (Nat.le_refl _)
    · show decide (1*(2*k) ≤ 2*(2*m - k)) = true
      rw [Nat.one_mul]
      apply decide_eq_true
      -- 2k ≤ 2(2m - k): want k ≤ 2m - k, i.e. 2k ≤ 2m, holds via h_km.
      have h_2k_2m : 2*k ≤ 2*m := Nat.mul_le_mul_left 2 h_km
      have h_k_2m : k ≤ 2*m :=
        Nat.le_trans h_km (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ 1))
      have h_k_2mk : k ≤ 2*m - k := by
        have h_kk_2m : k + k ≤ 2*m := by rw [← Nat.two_mul]; exact h_2k_2m
        have h_eq : k + (2*m - k) = 2*m :=
          E213.Tactic.Nat213.add_sub_of_le h_k_2m
        have h_kk_kSub : k + k ≤ k + (2*m - k) :=
          Eq.subst (motive := fun x => k + k ≤ x) h_eq.symm h_kk_2m
        exact E213.Tactic.Nat213.le_of_add_le_add_left h_kk_kSub
      exact Nat.mul_le_mul_left 2 h_k_2mk

/-- **cutSum (1/2) (1/2) ≡ constCut 1 1** (cutEq, PURE). -/
theorem cutSum_half_half :
    cutEq (cutSum (constCut 1 2) (constCut 1 2)) (constCut 1 1) :=
  cutSum_half_half_at

/-- **cutSum (1/3) (1/3) ≡ constCut 2 3** (cutEq, PURE). -/
theorem cutSum_third_third :
    cutEq (cutSum (constCut 1 3) (constCut 1 3)) (constCut 2 3) := by
  intro m k
  apply bool_eq_iff
  show cutSumAux (constCut 1 3) (constCut 1 3) k (2*m) (2*m) = true
       ↔ constCut 2 3 m k = true
  constructor
  · intro hLHS
    have hExt :=
      (cutSumAux_eq_true_iff (constCut 1 3) (constCut 1 3) k (2*m) (2*m)).mp hLHS
    obtain ⟨i, hi, hci, hcsi⟩ := hExt
    have h_2k_3i : 2*k ≤ 3*i := by
      have : 1*(2*k) ≤ 3*i := of_decide_eq_true hci
      rwa [Nat.one_mul] at this
    have h_2k_3mi : 2*k ≤ 3*(2*m - i) := by
      have : 1*(2*k) ≤ 3*(2*m - i) := of_decide_eq_true hcsi
      rwa [Nat.one_mul] at this
    show decide (2*k ≤ 3*m) = true
    apply decide_eq_true
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.Nat213.add_sub_of_le hi
    have h_sum : 3*i + 3*(2*m - i) = 3*(2*m) := by
      rw [← Nat.mul_add]; rw [h_add]
    have h_4k_3sum : 2*k + 2*k ≤ 3*i + 3*(2*m - i) := Nat.add_le_add h_2k_3i h_2k_3mi
    have h_4k_3_2m : 2*k + 2*k ≤ 3*(2*m) := h_sum ▸ h_4k_3sum
    have h_2_2k : 2*(2*k) ≤ 3*(2*m) := by rw [Nat.two_mul]; exact h_4k_3_2m
    have h_2_2k_3m : 2*(2*k) ≤ 2*(3*m) := by
      have e : 3*(2*m) = 2*(3*m) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm 3 2,
            E213.Tactic.Nat213.mul_assoc]
      rw [← e]; exact h_2_2k
    exact Nat.le_of_mul_le_mul_left h_2_2k_3m (by decide : 0 < 2)
  · intro h
    have h_2k_3m : 2*k ≤ 3*m := of_decide_eq_true h
    apply (cutSumAux_eq_true_iff (constCut 1 3) (constCut 1 3) k (2*m) (2*m)).mpr
    refine ⟨m, ?_, ?_, ?_⟩
    · -- m ≤ 2*m via Nat.le_mul_of_pos_left
      exact Nat.le_mul_of_pos_left m (by decide : 0 < 2)
    · show decide (1*(2*k) ≤ 3*m) = true
      rw [Nat.one_mul]
      exact decide_eq_true h_2k_3m
    · show decide (1*(2*k) ≤ 3*(2*m - m)) = true
      rw [Nat.one_mul]
      have hmm : 2*m - m = m := by
        rw [Nat.two_mul]; exact E213.Tactic.Nat213.add_sub_cancel_right m m
      rw [hmm]
      exact decide_eq_true h_2k_3m

/-- **cutSum (a/2) (b/2) = (a+b)/2** for any a, b. -/
theorem cutSum_half_general (a b : Nat) :
    cutEq (cutSum (constCut a 2) (constCut b 2)) (constCut (a + b) 2) := by
  intro m k
  apply bool_eq_iff
  show cutSumAux (constCut a 2) (constCut b 2) k (2*m) (2*m) = true
       ↔ constCut (a + b) 2 m k = true
  constructor
  · intro hLHS
    have hExt :=
      (cutSumAux_eq_true_iff (constCut a 2) (constCut b 2) k (2*m) (2*m)).mp hLHS
    obtain ⟨i, hi, hci, hcsi⟩ := hExt
    have h_2ak_2i : a*(2*k) ≤ 2*i := of_decide_eq_true hci
    have h_2bk_2mi : b*(2*k) ≤ 2*(2*m - i) := of_decide_eq_true hcsi
    show decide ((a+b)*k ≤ 2*m) = true
    apply decide_eq_true
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.Nat213.add_sub_of_le hi
    have h_e1 : a*(2*k) = 2*(a*k) := by
      rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
    have h_e2 : b*(2*k) = 2*(b*k) := by
      rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
    rw [h_e1] at h_2ak_2i
    rw [h_e2] at h_2bk_2mi
    have h_ak : a*k ≤ i := Nat.le_of_mul_le_mul_left h_2ak_2i (by decide : 0 < 2)
    have h_bk : b*k ≤ 2*m - i := Nat.le_of_mul_le_mul_left h_2bk_2mi (by decide : 0 < 2)
    have h_abk : a*k + b*k ≤ i + (2*m - i) := Nat.add_le_add h_ak h_bk
    rw [h_add] at h_abk
    rw [show a*k + b*k = (a+b)*k from (E213.Tactic.Nat213.add_mul a b k).symm] at h_abk
    exact h_abk
  · intro h
    have h_abk_2m : (a+b)*k ≤ 2*m := of_decide_eq_true h
    have h_ak_le_2m : a*k ≤ 2*m := by
      have : a*k ≤ (a+b)*k := by
        rw [E213.Tactic.Nat213.add_mul]; exact Nat.le_add_right _ _
      exact Nat.le_trans this h_abk_2m
    apply (cutSumAux_eq_true_iff (constCut a 2) (constCut b 2) k (2*m) (2*m)).mpr
    refine ⟨a*k, h_ak_le_2m, ?_, ?_⟩
    · show decide (a*(2*k) ≤ 2*(a*k)) = true
      apply decide_eq_true
      have : a*(2*k) = 2*(a*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
      rw [this]
      exact Nat.le_refl _
    · show decide (b*(2*k) ≤ 2*(2*m - a*k)) = true
      apply decide_eq_true
      have e1 : b*(2*k) = 2*(b*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
      rw [e1]
      have h_abk' : a*k + b*k ≤ 2*m := by
        rw [show a*k + b*k = (a+b)*k from (E213.Tactic.Nat213.add_mul a b k).symm]
        exact h_abk_2m
      have h_bk_sub : b*k ≤ 2*m - a*k := by
        have h_swap : b*k + a*k ≤ 2*m := by
          rw [Nat.add_comm]; exact h_abk'
        exact E213.Tactic.Nat213.le_sub_of_add_le h_swap
      exact Nat.mul_le_mul_left 2 h_bk_sub

/-- **cutSum (a/1) (b/2) = (2*a + b)/2** for any a, b. -/
theorem cutSum_int_half (a b : Nat) :
    cutEq (cutSum (constCut a 1) (constCut b 2)) (constCut (2*a + b) 2) := by
  intro m k
  apply bool_eq_iff
  show cutSumAux (constCut a 1) (constCut b 2) k (2*m) (2*m) = true
       ↔ constCut (2*a + b) 2 m k = true
  constructor
  · intro hLHS
    have hExt :=
      (cutSumAux_eq_true_iff (constCut a 1) (constCut b 2) k (2*m) (2*m)).mp hLHS
    obtain ⟨i, hi, hci, hcsi⟩ := hExt
    have h_2ak_i : 2*(a*k) ≤ i := by
      have h1 : a*(2*k) ≤ 1*i := of_decide_eq_true hci
      have e : a*(2*k) = 2*(a*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
      rw [Nat.one_mul] at h1; rwa [e] at h1
    have h_2bk_2mi : b*(2*k) ≤ 2*(2*m - i) := of_decide_eq_true hcsi
    show decide ((2*a + b)*k ≤ 2*m) = true
    apply decide_eq_true
    have h_bk : b*k ≤ 2*m - i := by
      have e : b*(2*k) = 2*(b*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
      rw [e] at h_2bk_2mi
      exact Nat.le_of_mul_le_mul_left h_2bk_2mi (by decide : 0 < 2)
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.Nat213.add_sub_of_le hi
    have h_total : 2*(a*k) + b*k ≤ 2*m := by
      calc 2*(a*k) + b*k ≤ i + (2*m - i) := Nat.add_le_add h_2ak_i h_bk
        _ = 2*m := h_add
    have e_lhs : (2*a + b)*k = 2*(a*k) + b*k := by
      rw [E213.Tactic.Nat213.add_mul, E213.Tactic.Nat213.mul_assoc]
    rw [e_lhs]
    exact h_total
  · intro h
    have h_le : (2*a + b)*k ≤ 2*m := of_decide_eq_true h
    have h_total : 2*(a*k) + b*k ≤ 2*m := by
      have e : (2*a + b)*k = 2*(a*k) + b*k := by
        rw [E213.Tactic.Nat213.add_mul, E213.Tactic.Nat213.mul_assoc]
      rw [e] at h_le; exact h_le
    apply (cutSumAux_eq_true_iff (constCut a 1) (constCut b 2) k (2*m) (2*m)).mpr
    refine ⟨2*(a*k), ?_, ?_, ?_⟩
    · -- 2*(a*k) ≤ 2*m
      have h_2ak_le : 2*(a*k) ≤ 2*(a*k) + b*k := Nat.le_add_right _ _
      exact Nat.le_trans h_2ak_le h_total
    · show decide (a*(2*k) ≤ 1*(2*(a*k))) = true
      rw [Nat.one_mul]
      have : a*(2*k) = 2*(a*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
      rw [this]
      exact decide_eq_true (Nat.le_refl _)
    · show decide (b*(2*k) ≤ 2*(2*m - 2*(a*k))) = true
      apply decide_eq_true
      have e : b*(2*k) = 2*(b*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
      rw [e]
      have h_bk_sub : b*k ≤ 2*m - 2*(a*k) := by
        have h_swap : b*k + 2*(a*k) ≤ 2*m := by
          rw [Nat.add_comm]; exact h_total
        exact E213.Tactic.Nat213.le_sub_of_add_le h_swap
      exact Nat.mul_le_mul_left 2 h_bk_sub

/-- **cutSum (a/2) (b/1) ≡ (a + 2*b)/2** (cutEq, half + int via comm, PURE). -/
theorem cutSum_half_int (a b : Nat) :
    cutEq (cutSum (constCut a 2) (constCut b 1)) (constCut (a + 2*b) 2) := by
  intro m k
  rw [cutSum_comm]
  rw [cutSum_int_half b a m k, Nat.add_comm (2*b) a]

/-- **cutSum (a/1) (b/1) = (a+b)/1** for integers. -/
theorem cutSum_int_int (a b : Nat) :
    cutEq (cutSum (constCut a 1) (constCut b 1)) (constCut (a + b) 1) := by
  intro m k
  apply bool_eq_iff
  show cutSumAux (constCut a 1) (constCut b 1) k (2*m) (2*m) = true
       ↔ constCut (a + b) 1 m k = true
  constructor
  · intro hLHS
    have hExt :=
      (cutSumAux_eq_true_iff (constCut a 1) (constCut b 1) k (2*m) (2*m)).mp hLHS
    obtain ⟨i, hi, hci, hcsi⟩ := hExt
    have h_2ak_i : 2*(a*k) ≤ i := by
      have : a*(2*k) ≤ 1*i := of_decide_eq_true hci
      rw [Nat.one_mul] at this
      have e : a*(2*k) = 2*(a*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
      rwa [e] at this
    have h_2bk_2mi : 2*(b*k) ≤ 2*m - i := by
      have : b*(2*k) ≤ 1*(2*m - i) := of_decide_eq_true hcsi
      rw [Nat.one_mul] at this
      have e : b*(2*k) = 2*(b*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
      rwa [e] at this
    show decide ((a+b)*k ≤ 1*m) = true
    rw [Nat.one_mul]
    apply decide_eq_true
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.Nat213.add_sub_of_le hi
    have h_2abk_2m : 2*(a*k) + 2*(b*k) ≤ 2*m := by
      calc 2*(a*k) + 2*(b*k)
          ≤ i + (2*m - i) := Nat.add_le_add h_2ak_i h_2bk_2mi
        _ = 2*m := h_add
    have e : 2*(a*k) + 2*(b*k) = 2 * ((a+b)*k) := by
      rw [← Nat.mul_add, E213.Tactic.Nat213.add_mul]
    rw [e] at h_2abk_2m
    exact Nat.le_of_mul_le_mul_left h_2abk_2m (by decide : 0 < 2)
  · intro h
    have h_abk_m : (a+b)*k ≤ 1*m := of_decide_eq_true h
    rw [Nat.one_mul] at h_abk_m
    have h_ak_m : a*k ≤ m := by
      have : a*k ≤ (a+b)*k := by
        rw [E213.Tactic.Nat213.add_mul]; exact Nat.le_add_right _ _
      exact Nat.le_trans this h_abk_m
    have h_bk_m : b*k ≤ m := by
      have : b*k ≤ (a+b)*k := by
        rw [E213.Tactic.Nat213.add_mul, Nat.add_comm]; exact Nat.le_add_right _ _
      exact Nat.le_trans this h_abk_m
    apply (cutSumAux_eq_true_iff (constCut a 1) (constCut b 1) k (2*m) (2*m)).mpr
    refine ⟨2*(a*k), ?_, ?_, ?_⟩
    · -- 2ak ≤ 2m, since ak ≤ m
      exact Nat.mul_le_mul_left 2 h_ak_m
    · show decide (a*(2*k) ≤ 1*(2*(a*k))) = true
      rw [Nat.one_mul]
      have e : a*(2*k) = 2*(a*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc]
      rw [e]
      exact decide_eq_true (Nat.le_refl _)
    · show decide (b*(2*k) ≤ 1*(2*m - 2*(a*k))) = true
      rw [Nat.one_mul]
      apply decide_eq_true
      have e : b*(2*k) = 2*(b*k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc]
      rw [e]
      have h_2bk_sub : 2*(b*k) ≤ 2*m - 2*(a*k) := by
        have h_sum : 2*(b*k) + 2*(a*k) ≤ 2*m := by
          have e2 : 2*(b*k) + 2*(a*k) = 2*(b*k + a*k) := (Nat.mul_add 2 _ _).symm
          rw [e2]
          have h_abk_le_m : a*k + b*k ≤ m := by
            rw [show a*k + b*k = (a+b)*k from (E213.Tactic.Nat213.add_mul a b k).symm]
            exact h_abk_m
          have h_ba_le_m : b*k + a*k ≤ m := by rw [Nat.add_comm]; exact h_abk_le_m
          exact Nat.mul_le_mul_left 2 h_ba_le_m
        exact E213.Tactic.Nat213.le_sub_of_add_le h_sum
      exact h_2bk_sub

/-- **Pointwise** version of `cutSum_self`: ∅-axiom (no funext, no
    `rw [iff]`).  Uses `Iff.mp` / `Iff.mpr` directly to avoid
    propext leak from `rw` on Iff. -/
theorem cutSum_self_at (a b : Nat) (m k : Nat) :
    cutSum (constCut a b) (constCut a b) m k = constCut (2*a) b m k := by
  apply bool_eq_iff
  show cutSumAux (constCut a b) (constCut a b) k (2*m) (2*m) = true
       ↔ constCut (2*a) b m k = true
  have e_a2k : a * (2*k) = 2 * (a*k) := by
    rw [Nat.mul_comm a (2*k), E213.Tactic.Nat213.mul_assoc, Nat.mul_comm k a]
  have e_b2m : b * (2*m) = 2 * (b*m) := by
    rw [Nat.mul_comm b (2*m), E213.Tactic.Nat213.mul_assoc, Nat.mul_comm m b]
  have e_2ak : (2*a)*k = 2*(a*k) := E213.Tactic.Nat213.mul_assoc 2 a k
  constructor
  · intro hLHS
    have hExt := (cutSumAux_eq_true_iff (constCut a b) (constCut a b)
                    k (2*m) (2*m)).mp hLHS
    obtain ⟨i, hi, hci, hcsi⟩ := hExt
    have h_a2k_bi : a*(2*k) ≤ b*i := of_decide_eq_true hci
    have h_a2k_b2mi : a*(2*k) ≤ b*(2*m - i) := of_decide_eq_true hcsi
    show decide ((2*a)*k ≤ b*m) = true
    apply decide_eq_true
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.Nat213.add_sub_of_le hi
    have h_sum_2bm : b*i + b*(2*m - i) = b*(2*m) := by
      rw [← Nat.mul_add, h_add]
    have h_2_a2k : 2 * (a*(2*k)) ≤ b*(2*m) := by
      calc 2 * (a*(2*k)) = a*(2*k) + a*(2*k) := Nat.two_mul _
        _ ≤ b*i + b*(2*m - i) := Nat.add_le_add h_a2k_bi h_a2k_b2mi
        _ = b*(2*m) := h_sum_2bm
    rw [e_a2k, e_b2m] at h_2_a2k
    have h_2ak_bm : 2 * (a*k) ≤ b*m :=
      Nat.le_of_mul_le_mul_left h_2_a2k (Nat.zero_lt_succ 1)
    rw [e_2ak]; exact h_2ak_bm
  · intro h
    have h_2ak_bm : (2*a)*k ≤ b*m := of_decide_eq_true h
    rw [e_2ak] at h_2ak_bm
    have h_a2k_bm : a*(2*k) ≤ b*m := by rw [e_a2k]; exact h_2ak_bm
    apply (cutSumAux_eq_true_iff (constCut a b) (constCut a b)
            k (2*m) (2*m)).mpr
    refine ⟨m, ?_, ?_, ?_⟩
    · show m ≤ 2*m
      have hm : 2*m = m + m := Nat.two_mul m
      rw [hm]; exact Nat.le_add_right m m
    · show decide (a*(2*k) ≤ b*m) = true
      exact decide_eq_true h_a2k_bm
    · show decide (a*(2*k) ≤ b*(2*m - m)) = true
      have h_2mm : 2*m - m = m := by
        rw [Nat.two_mul]; exact E213.Tactic.Nat213.add_sub_cancel_right m m
      rw [h_2mm]
      exact decide_eq_true h_a2k_bm

/-- **cutSum c c ≡ 2c** for constant cut c = a/b (cutEq, PURE). -/
theorem cutSum_self (a b : Nat) :
    cutEq (cutSum (constCut a b) (constCut a b)) (constCut (2*a) b) :=
  cutSum_self_at a b

end E213.Math.Real213.CutSumOne
