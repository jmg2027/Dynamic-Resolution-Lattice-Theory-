import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulComm
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm
import E213.Meta.Tactic.BoolHelper

import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
/-!
# CutMulOne: cutMul (1)(1) = constCut 1 1 (general theorem)

via iff existential characterization + Nat arithmetic on bounds.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mul.CutMulOne

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul cutMulInner cutMulOuter)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMulComm (cutMulOuter_eq_true_iff cutMul_comm)

open E213.Tactic.BoolHelper (bool_eq_iff)

/-- **cutMul (1)(1) = constCut 1 1** pointwise (∅-axiom).  Avoids
    `funext` and `rw [iff]` (both propext-laden). -/
theorem cutMul_one_one_at (m k : Nat) :
    cutMul (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k := by
  apply bool_eq_iff
  refine Iff.trans (cutMulOuter_eq_true_iff _ _ k m _ _) ?_
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

/-- **cutMul (1) (constCut a b) = constCut a b** pointwise (∅-axiom). -/
theorem cutMul_one_const_at (a b m k : Nat) :
    cutMul (constCut 1 1) (constCut a b) m k = constCut a b m k := by
  apply bool_eq_iff
  refine Iff.trans (cutMulOuter_eq_true_iff _ _ k m _ _) ?_
  constructor
  · rintro ⟨m1, _, m2, _, hcx, hcy, hmul⟩
    have h_m1 : k ≤ m1 := by
      have : 1*k ≤ 1*m1 := of_decide_eq_true hcx
      rwa [Nat.one_mul, Nat.one_mul] at this
    have h_m2 : a*k ≤ b*m2 := of_decide_eq_true hcy
    -- From m1 ≥ k: k*m2 ≤ m1*m2 ≤ m*k.  So k*m2 ≤ m*k.
    have h_km2 : k*m2 ≤ m*k :=
      Nat.le_trans (Nat.mul_le_mul_right m2 h_m1) hmul
    -- k*m2 ≤ m*k = k*m, so m2 ≤ m (when k > 0).  When k = 0: k*m2 = 0, but
    -- need a*k ≤ b*m. a*0 = 0 ≤ bm. ✓
    show decide (a*k ≤ b*m) = true
    apply decide_eq_true
    cases k with
    | zero =>
      rw [Nat.mul_zero]; exact Nat.zero_le _
    | succ j =>
      have h_m2_le_m : m2 ≤ m := by
        have : (j+1) * m2 ≤ (j+1) * m := by
          rw [show m * (j+1) = (j+1) * m from Nat.mul_comm _ _] at h_km2
          exact h_km2
        exact Nat.le_of_mul_le_mul_left this (Nat.succ_pos _)
      exact Nat.le_trans h_m2 (Nat.mul_le_mul_left b h_m2_le_m)
  · intro h
    have h_ak : a*k ≤ b*m := of_decide_eq_true h
    have hk_bound : k ≤ (m+1)*(k+1) :=
      Nat.le_trans (Nat.le_succ k)
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hm_bound : m ≤ (m+1)*(k+1) := by
      calc m ≤ m+1 := Nat.le_succ m
        _ ≤ (m+1)*(k+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    refine ⟨k, hk_bound, m, hm_bound, ?_, ?_, ?_⟩
    · show decide (1*k ≤ 1*k) = true
      exact decide_eq_true (Nat.le_refl _)
    · show decide (a*k ≤ b*m) = true
      exact decide_eq_true h_ak
    · -- k*m ≤ m*k
      rw [Nat.mul_comm]; exact Nat.le_refl _

/-- **cutMul (constCut a b) (constCut 1 1) = constCut a b** pointwise (∅-axiom). -/
theorem cutMul_const_one_at (a b m k : Nat) :
    cutMul (constCut a b) (constCut 1 1) m k = constCut a b m k := by
  rw [cutMul_comm (constCut a b) (constCut 1 1) m k]
  exact cutMul_one_const_at a b m k

end E213.Lib.Math.NumberSystems.Real213.Mul.CutMulOne
