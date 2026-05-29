import E213.Meta.Tactic.BoolHelper
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.Real213.Sum.CutSumComm
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Lib.Math.Real213.Core.CutPoset

import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# CutSumOne: cutSum (constCut a₁ b₁) (constCut a₂ b₂) = constCut X Y identities

8 instances (one_one, zero_const, half_half, third_third, half_general,
int_half, int_int, self) all share a bidirectional iff opener
(constructor + obtain ⟨i, hi, hci, hcsi⟩) and a `decide_eq_true` closer.
The differences are purely the per-instance arithmetic content.

`cutSum_constCut_at` ( C — Part 4 marathon) extracts that
opener + closer as a 3-component template: caller supplies a
**forward** function (extract `X*k ≤ Y*m` from the witness `i ≤ 2*m`
and the two inequalities) and a **backward** function (construct the
witness from `X*k ≤ Y*m`).
-/

namespace E213.Lib.Math.Real213.Sum.CutSumOne

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Sum.CutSum (cutSum cutSumAux)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Sum.CutSumComm (cutSumAux_eq_true_iff cutSum_comm)
open E213.Lib.Math.Real213.Core.CutPoset (cutEq)

open E213.Tactic.BoolHelper (bool_eq_iff)

/-- ★ 3-component template ( C).  Bidirectional iff opener +
    `decide_eq_true` closer for `cutSum (constCut a₁ b₁) (constCut a₂ b₂)
    m k = constCut X Y m k`.  Caller supplies per-instance arithmetic
    forward/backward bodies. -/
theorem cutSum_constCut_at
    (a₁ b₁ a₂ b₂ X Y m k : Nat)
    (forward : ∀ i, i ≤ 2*m →
                a₁*(2*k) ≤ b₁*i →
                a₂*(2*k) ≤ b₂*(2*m - i) →
                X*k ≤ Y*m)
    (backward : X*k ≤ Y*m →
                ∃ i, i ≤ 2*m ∧ a₁*(2*k) ≤ b₁*i ∧ a₂*(2*k) ≤ b₂*(2*m - i)) :
    cutSum (constCut a₁ b₁) (constCut a₂ b₂) m k = constCut X Y m k := by
  apply bool_eq_iff
  show cutSumAux (constCut a₁ b₁) (constCut a₂ b₂) k (2*m) (2*m) = true
       ↔ constCut X Y m k = true
  constructor
  · intro hLHS
    obtain ⟨i, hi, hci, hcsi⟩ :=
      (cutSumAux_eq_true_iff (constCut a₁ b₁) (constCut a₂ b₂) k (2*m) (2*m)).mp hLHS
    exact decide_eq_true
      (forward i hi (of_decide_eq_true hci) (of_decide_eq_true hcsi))
  · intro h
    obtain ⟨i, hi, h_ci, h_csi⟩ := backward (of_decide_eq_true h)
    refine (cutSumAux_eq_true_iff (constCut a₁ b₁) (constCut a₂ b₂) k (2*m) (2*m)).mpr
      ⟨i, hi, decide_eq_true h_ci, decide_eq_true h_csi⟩

/-- **cutSum (1)(1) = constCut 2 1**: 1 + 1 = 2 as cut function.  PURE. -/
theorem cutSum_one_one :
    cutEq (cutSum (constCut 1 1) (constCut 1 1)) (constCut 2 1) := by
  intro m k
  refine cutSum_constCut_at 1 1 1 1 2 1 m k ?_ ?_
  · intro i hi h₁ h₂
    rw [Nat.one_mul, Nat.one_mul] at h₁
    rw [Nat.one_mul, Nat.one_mul] at h₂
    rw [Nat.one_mul]
    have h_kk : 2*k + 2*k ≤ i + (2*m - i) := Nat.add_le_add h₁ h₂
    rw [E213.Tactic.NatHelper.add_sub_of_le hi] at h_kk
    have h2 : 2*(2*k) ≤ 2*m := by rw [Nat.two_mul]; exact h_kk
    exact Nat.le_of_mul_le_mul_left h2 (by decide : 0 < 2)
  · intro h
    rw [Nat.one_mul] at h
    refine ⟨2*k, ?_, Nat.le_refl _, ?_⟩
    · exact Nat.le_trans h (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
    · rw [Nat.one_mul, Nat.one_mul]
      have h_4k : 2*(2*k) ≤ 2*m := Nat.mul_le_mul_left 2 h
      have h_kk : 2*k + 2*k ≤ 2*m := by rw [← Nat.two_mul]; exact h_4k
      exact E213.Tactic.NatHelper.le_sub_of_add_le h_kk

/-- **cutSum (0)(constCut a b) ≡ constCut a b** (cutEq, zero left identity, PURE). -/
theorem cutSum_zero_const (a b : Nat) :
    cutEq (cutSum (constCut 0 1) (constCut a b)) (constCut a b) := by
  intro m k
  refine cutSum_constCut_at 0 1 a b a b m k ?_ ?_
  · intro i _ _ h_csi
    have h1 : a*(2*k) ≤ b*(2*m) :=
      Nat.le_trans h_csi (Nat.mul_le_mul_left b (Nat.sub_le _ _))
    have e1 : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
    have e2 : b*(2*m) = 2*(b*m) := by rw [E213.Tactic.NatHelper.mul_left_comm]
    rw [e1, e2] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by decide : 0 < 2)
  · intro h
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · rw [Nat.zero_mul]; exact Nat.zero_le _
    · rw [Nat.sub_zero]
      have e1 : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      have e2 : b*(2*m) = 2*(b*m) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e1, e2]; exact Nat.mul_le_mul_left 2 h

/-- **cutSum (constCut a b) (constCut 0 1) ≡ constCut a b**
    (cutEq, right zero identity, PURE).  Via cutSum_comm + cutSum_zero_const. -/
theorem cutSum_const_zero (a b : Nat) :
    cutEq (cutSum (constCut a b) (constCut 0 1)) (constCut a b) := by
  intro m k
  rw [cutSum_comm (constCut a b) (constCut 0 1) m k]
  exact cutSum_zero_const a b m k

/-- **cutSum (1/2) (1/2) = constCut 1 1** pointwise (∅-axiom). -/
theorem cutSum_half_half_at (m k : Nat) :
    cutSum (constCut 1 2) (constCut 1 2) m k = constCut 1 1 m k := by
  refine cutSum_constCut_at 1 2 1 2 1 1 m k ?_ ?_
  · intro i hi h₁ h₂
    rw [Nat.one_mul] at h₁
    rw [Nat.one_mul] at h₂
    rw [Nat.one_mul, Nat.one_mul]
    have h_k_i : k ≤ i := Nat.le_of_mul_le_mul_left h₁ (by decide : 0 < 2)
    have h_k_mi : k ≤ 2*m - i := Nat.le_of_mul_le_mul_left h₂ (by decide : 0 < 2)
    have h_kk : k + k ≤ i + (2*m - i) := Nat.add_le_add h_k_i h_k_mi
    rw [E213.Tactic.NatHelper.add_sub_of_le hi] at h_kk
    have h_2k_2m : 2*k ≤ 2*m := by rw [Nat.two_mul]; exact h_kk
    exact Nat.le_of_mul_le_mul_left h_2k_2m (by decide : 0 < 2)
  · intro h
    rw [Nat.one_mul, Nat.one_mul] at h
    refine ⟨k, ?_, ?_, ?_⟩
    · exact Nat.le_trans h (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
    · rw [Nat.one_mul]; exact Nat.le_refl _
    · rw [Nat.one_mul]
      have h_2k_2m : 2*k ≤ 2*m := Nat.mul_le_mul_left 2 h
      have h_kk : k + k ≤ 2*m := by rw [← Nat.two_mul]; exact h_2k_2m
      have h_k_sub : k ≤ 2*m - k :=
        E213.Tactic.NatHelper.le_sub_of_add_le h_kk
      exact Nat.mul_le_mul_left 2 h_k_sub

/-- **cutSum (1/2) (1/2) ≡ constCut 1 1** (cutEq, PURE). -/
theorem cutSum_half_half :
    cutEq (cutSum (constCut 1 2) (constCut 1 2)) (constCut 1 1) :=
  cutSum_half_half_at

/-- **cutSum (1/3) (1/3) ≡ constCut 2 3** (cutEq, PURE). -/
theorem cutSum_third_third :
    cutEq (cutSum (constCut 1 3) (constCut 1 3)) (constCut 2 3) := by
  intro m k
  refine cutSum_constCut_at 1 3 1 3 2 3 m k ?_ ?_
  · intro i hi h₁ h₂
    rw [Nat.one_mul] at h₁
    rw [Nat.one_mul] at h₂
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.NatHelper.add_sub_of_le hi
    have h_sum : 3*i + 3*(2*m - i) = 3*(2*m) := by rw [← Nat.mul_add]; rw [h_add]
    have h_kk : 2*k + 2*k ≤ 3*i + 3*(2*m - i) := Nat.add_le_add h₁ h₂
    have h_2_2k_3_2m : 2*(2*k) ≤ 3*(2*m) := by rw [Nat.two_mul]; rw [← h_sum]; exact h_kk
    have e : 3*(2*m) = 2*(3*m) := by
      rw [← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm 3 2,
          E213.Tactic.NatHelper.mul_assoc]
    rw [e] at h_2_2k_3_2m
    exact Nat.le_of_mul_le_mul_left h_2_2k_3_2m (by decide : 0 < 2)
  · intro h
    refine ⟨m, ?_, ?_, ?_⟩
    · exact Nat.le_mul_of_pos_left m (by decide : 0 < 2)
    · rw [Nat.one_mul]; exact h
    · rw [Nat.one_mul]
      have hmm : 2*m - m = m := by
        rw [Nat.two_mul]; exact E213.Tactic.NatHelper.add_sub_cancel_right m m
      rw [hmm]; exact h

/-- **cutSum (a/2) (b/2) = (a+b)/2** for any a, b. -/
theorem cutSum_half_general (a b : Nat) :
    cutEq (cutSum (constCut a 2) (constCut b 2)) (constCut (a + b) 2) := by
  intro m k
  refine cutSum_constCut_at a 2 b 2 (a+b) 2 m k ?_ ?_
  · intro i hi h_ci h_csi
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.NatHelper.add_sub_of_le hi
    have h_e1 : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
    have h_e2 : b*(2*k) = 2*(b*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
    rw [h_e1] at h_ci
    rw [h_e2] at h_csi
    have h_ak : a*k ≤ i := Nat.le_of_mul_le_mul_left h_ci (by decide : 0 < 2)
    have h_bk : b*k ≤ 2*m - i := Nat.le_of_mul_le_mul_left h_csi (by decide : 0 < 2)
    have h_abk : a*k + b*k ≤ i + (2*m - i) := Nat.add_le_add h_ak h_bk
    rw [h_add] at h_abk
    rw [show a*k + b*k = (a+b)*k from (E213.Tactic.NatHelper.add_mul a b k).symm] at h_abk
    exact h_abk
  · intro h
    have h_ak_le_2m : a*k ≤ 2*m := by
      have : a*k ≤ (a+b)*k := by
        rw [E213.Tactic.NatHelper.add_mul]; exact Nat.le_add_right _ _
      exact Nat.le_trans this h
    refine ⟨a*k, h_ak_le_2m, ?_, ?_⟩
    · have e1 : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e1]; exact Nat.le_refl _
    · have e1 : b*(2*k) = 2*(b*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e1]
      have h_abk' : a*k + b*k ≤ 2*m := by
        rw [show a*k + b*k = (a+b)*k from (E213.Tactic.NatHelper.add_mul a b k).symm]
        exact h
      have h_bk_sub : b*k ≤ 2*m - a*k := by
        have h_swap : b*k + a*k ≤ 2*m := by rw [Nat.add_comm]; exact h_abk'
        exact E213.Tactic.NatHelper.le_sub_of_add_le h_swap
      exact Nat.mul_le_mul_left 2 h_bk_sub

/-- **cutSum (a/1) (b/2) = (2*a + b)/2** for any a, b. -/
theorem cutSum_int_half (a b : Nat) :
    cutEq (cutSum (constCut a 1) (constCut b 2)) (constCut (2*a + b) 2) := by
  intro m k
  refine cutSum_constCut_at a 1 b 2 (2*a + b) 2 m k ?_ ?_
  · intro i hi h_ci h_csi
    have h_2ak_i : 2*(a*k) ≤ i := by
      rw [Nat.one_mul] at h_ci
      have e : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rwa [e] at h_ci
    have h_bk : b*k ≤ 2*m - i := by
      have e : b*(2*k) = 2*(b*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e] at h_csi
      exact Nat.le_of_mul_le_mul_left h_csi (by decide : 0 < 2)
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.NatHelper.add_sub_of_le hi
    have h_total : 2*(a*k) + b*k ≤ 2*m := by
      calc 2*(a*k) + b*k ≤ i + (2*m - i) := Nat.add_le_add h_2ak_i h_bk
        _ = 2*m := h_add
    have e_lhs : (2*a + b)*k = 2*(a*k) + b*k := by
      rw [E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.mul_assoc]
    rw [e_lhs]; exact h_total
  · intro h
    have h_total : 2*(a*k) + b*k ≤ 2*m := by
      have e : (2*a + b)*k = 2*(a*k) + b*k := by
        rw [E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.mul_assoc]
      rw [e] at h; exact h
    refine ⟨2*(a*k), Nat.le_trans (Nat.le_add_right _ _) h_total, ?_, ?_⟩
    · rw [Nat.one_mul]
      have e : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e]; exact Nat.le_refl _
    · have e : b*(2*k) = 2*(b*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e]
      have h_bk_sub : b*k ≤ 2*m - 2*(a*k) := by
        have h_swap : b*k + 2*(a*k) ≤ 2*m := by rw [Nat.add_comm]; exact h_total
        exact E213.Tactic.NatHelper.le_sub_of_add_le h_swap
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
  refine cutSum_constCut_at a 1 b 1 (a+b) 1 m k ?_ ?_
  · intro i hi h_ci h_csi
    rw [Nat.one_mul] at h_ci
    rw [Nat.one_mul] at h_csi
    have h_2ak_i : 2*(a*k) ≤ i := by
      have e : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rwa [e] at h_ci
    have h_2bk_2mi : 2*(b*k) ≤ 2*m - i := by
      have e : b*(2*k) = 2*(b*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rwa [e] at h_csi
    rw [Nat.one_mul]
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.NatHelper.add_sub_of_le hi
    have h_2abk_2m : 2*(a*k) + 2*(b*k) ≤ 2*m := by
      calc 2*(a*k) + 2*(b*k)
          ≤ i + (2*m - i) := Nat.add_le_add h_2ak_i h_2bk_2mi
        _ = 2*m := h_add
    have e : 2*(a*k) + 2*(b*k) = 2 * ((a+b)*k) := by
      rw [← Nat.mul_add, E213.Tactic.NatHelper.add_mul]
    rw [e] at h_2abk_2m
    exact Nat.le_of_mul_le_mul_left h_2abk_2m (by decide : 0 < 2)
  · intro h
    rw [Nat.one_mul] at h
    have h_ak_m : a*k ≤ m := by
      have : a*k ≤ (a+b)*k := by
        rw [E213.Tactic.NatHelper.add_mul]; exact Nat.le_add_right _ _
      exact Nat.le_trans this h
    refine ⟨2*(a*k), ?_, ?_, ?_⟩
    · exact Nat.mul_le_mul_left 2 h_ak_m
    · rw [Nat.one_mul]
      have e : a*(2*k) = 2*(a*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e]; exact Nat.le_refl _
    · rw [Nat.one_mul]
      have e : b*(2*k) = 2*(b*k) := by rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e]
      have h_2bk_sub : 2*(b*k) ≤ 2*m - 2*(a*k) := by
        have h_sum : 2*(b*k) + 2*(a*k) ≤ 2*m := by
          have e2 : 2*(b*k) + 2*(a*k) = 2*(b*k + a*k) := (Nat.mul_add 2 _ _).symm
          rw [e2]
          have h_abk_le_m : a*k + b*k ≤ m := by
            rw [show a*k + b*k = (a+b)*k from (E213.Tactic.NatHelper.add_mul a b k).symm]
            exact h
          have h_ba_le_m : b*k + a*k ≤ m := by rw [Nat.add_comm]; exact h_abk_le_m
          exact Nat.mul_le_mul_left 2 h_ba_le_m
        exact E213.Tactic.NatHelper.le_sub_of_add_le h_sum
      exact h_2bk_sub

/-- **Pointwise** `cutSum (a/b)(a/b) = (2a)/b`: ∅-axiom. -/
theorem cutSum_self_at (a b : Nat) (m k : Nat) :
    cutSum (constCut a b) (constCut a b) m k = constCut (2*a) b m k := by
  refine cutSum_constCut_at a b a b (2*a) b m k ?_ ?_
  · intro i hi h_ci h_csi
    have h_add : i + (2*m - i) = 2*m := E213.Tactic.NatHelper.add_sub_of_le hi
    have h_sum_2bm : b*i + b*(2*m - i) = b*(2*m) := by rw [← Nat.mul_add, h_add]
    have h_2_a2k : 2 * (a*(2*k)) ≤ b*(2*m) := by
      calc 2 * (a*(2*k)) = a*(2*k) + a*(2*k) := Nat.two_mul _
        _ ≤ b*i + b*(2*m - i) := Nat.add_le_add h_ci h_csi
        _ = b*(2*m) := h_sum_2bm
    have e_a2k : a * (2*k) = 2 * (a*k) := by
      rw [Nat.mul_comm a (2*k), E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm k a]
    have e_b2m : b * (2*m) = 2 * (b*m) := by
      rw [Nat.mul_comm b (2*m), E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm m b]
    rw [e_a2k, e_b2m] at h_2_a2k
    have h_2ak_bm : 2 * (a*k) ≤ b*m :=
      Nat.le_of_mul_le_mul_left h_2_a2k (Nat.zero_lt_succ 1)
    rw [E213.Tactic.NatHelper.mul_assoc 2 a k]; exact h_2ak_bm
  · intro h
    have e_a2k : a * (2*k) = 2 * (a*k) := by
      rw [Nat.mul_comm a (2*k), E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm k a]
    rw [E213.Tactic.NatHelper.mul_assoc 2 a k] at h
    have h_a2k_bm : a*(2*k) ≤ b*m := by rw [e_a2k]; exact h
    refine ⟨m, ?_, h_a2k_bm, ?_⟩
    · have hm : 2*m = m + m := Nat.two_mul m
      rw [hm]; exact Nat.le_add_right m m
    · have h_2mm : 2*m - m = m := by
        rw [Nat.two_mul]; exact E213.Tactic.NatHelper.add_sub_cancel_right m m
      rw [h_2mm]; exact h_a2k_bm

/-- **cutSum c c ≡ 2c** for constant cut c = a/b (cutEq, PURE). -/
theorem cutSum_self (a b : Nat) :
    cutEq (cutSum (constCut a b) (constCut a b)) (constCut (2*a) b) :=
  cutSum_self_at a b

end E213.Lib.Math.Real213.Sum.CutSumOne
