import E213.Kernel.Tactic.Nat213
import E213.Math.Real213.CutSumOne
import E213.Math.Real213.ConstCutScale
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutSumZero

/-!
# Research.Real213CutMidSelf: midpoint(c, c) = c for const cut

cutMid (constCut a b) (constCut a b) = constCut a b for b ≥ 1.

Via cutSum_self + cutHalf_constCut + constCut_scale.
-/

namespace E213.Math.Real213.CutMidSelf

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutHalf cutHalf_constCut cutHalf_constCut_at cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumOne (cutSum_self cutSum_self_at)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.ConstCutScale (constCut_scale constCut_scale_at)
open E213.Math.Real213.CutSumOne
  (cutSum_half_general cutSum_int_int cutSum_int_half cutSum_half_int)
open E213.Math.Real213.CutMulOne (cutMul_one_const cutMul_const_one cutMul_one_one)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero)

private theorem bool_eq_iff_local (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **midpoint(c, c) = c** for c = a/b — pointwise (∅-axiom). -/
theorem cutMid_self_constCut_at (a b m k : Nat) (_hb : b ≥ 1) :
    cutMid (constCut a b) (constCut a b) m k = constCut a b m k := by
  show cutHalf (cutSum (constCut a b) (constCut a b)) m k = constCut a b m k
  show cutSum (constCut a b) (constCut a b) (2*m) k = constCut a b m k
  rw [cutSum_self_at]
  -- Goal: constCut (2*a) b (2*m) k = constCut a b m k
  -- = decide ((2*a)*k ≤ b*(2*m)) = decide (a*k ≤ b*m)
  apply bool_eq_iff_local
  constructor
  · intro h
    have h1 : (2*a)*k ≤ b*(2*m) := of_decide_eq_true h
    have h2 : 2*(a*k) ≤ 2*(b*m) := by
      rw [E213.Tactic.Nat213.mul_assoc] at h1
      rw [show b*(2*m) = 2*(b*m) from by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b 2, E213.Tactic.Nat213.mul_assoc]] at h1
      exact h1
    exact decide_eq_true
      (Nat.le_of_mul_le_mul_left h2 (Nat.zero_lt_succ 1))
  · intro h
    have h1 : a*k ≤ b*m := of_decide_eq_true h
    have h2 : 2*(a*k) ≤ 2*(b*m) := Nat.mul_le_mul_left 2 h1
    apply decide_eq_true
    rw [E213.Tactic.Nat213.mul_assoc, show b*(2*m) = 2*(b*m) from by
      rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b 2, E213.Tactic.Nat213.mul_assoc]]
    exact h2

/-- **midpoint(c, c) = c** for c = a/b. -/
theorem cutMid_self_constCut (a b : Nat) (hb : b ≥ 1) :
    cutMid (constCut a b) (constCut a b) = constCut a b := by
  funext m k
  exact cutMid_self_constCut_at a b m k hb

/-- **midpoint(a/2, c/2) = (a+c)/4** for any a, c. -/
theorem cutMid_half_general (a c : Nat) :
    cutMid (constCut a 2) (constCut c 2) = constCut (a+c) 4 := by
  show cutHalf (cutSum (constCut a 2) (constCut c 2)) = constCut (a+c) 4
  rw [cutSum_half_general, cutHalf_constCut]

/-- **midpoint(a/1, c/1) = (a+c)/2** for any integers a, c. -/
theorem cutMid_int_int (a c : Nat) :
    cutMid (constCut a 1) (constCut c 1) = constCut (a+c) 2 := by
  show cutHalf (cutSum (constCut a 1) (constCut c 1)) = constCut (a+c) 2
  rw [cutSum_int_int, cutHalf_constCut]

/-- **midpoint(a/1, c/2) = (2a+c)/4**. -/
theorem cutMid_int_half (a c : Nat) :
    cutMid (constCut a 1) (constCut c 2) = constCut (2*a+c) 4 := by
  show cutHalf (cutSum (constCut a 1) (constCut c 2)) = constCut (2*a+c) 4
  rw [cutSum_int_half, cutHalf_constCut]

/-- **midpoint(a/2, c/1) = (a+2c)/4**. -/
theorem cutMid_half_int (a c : Nat) :
    cutMid (constCut a 2) (constCut c 1) = constCut (a+2*c) 4 := by
  show cutHalf (cutSum (constCut a 2) (constCut c 1)) = constCut (a+2*c) 4
  rw [cutSum_half_int, cutHalf_constCut]

/-! ### Concrete cutMid evaluations on integer pairs -/

/-- midpoint(0, 1) = 1/2. -/
example : cutMid (constCut 0 1) (constCut 1 1) = constCut 1 2 :=
  cutMid_int_int 0 1

/-- midpoint(0, 4) = 2. -/
example : cutMid (constCut 0 1) (constCut 4 1) = constCut 4 2 :=
  cutMid_int_int 0 4

/-- midpoint(1, 3) = 2. -/
example : cutMid (constCut 1 1) (constCut 3 1) = constCut 4 2 :=
  cutMid_int_int 1 3

/-- midpoint(2, 8) = 5. -/
example : cutMid (constCut 2 1) (constCut 8 1) = constCut 10 2 :=
  cutMid_int_int 2 8

/-! ### Y2: cutMul concrete applications -/

/-- 1 × (5/7) = 5/7. -/
example : cutMul (constCut 1 1) (constCut 5 7) = constCut 5 7 :=
  cutMul_one_const 5 7

/-- (3/4) × 1 = 3/4. -/
example : cutMul (constCut 3 4) (constCut 1 1) = constCut 3 4 :=
  cutMul_const_one 3 4

/-- 0 × 0 = 0. -/
example : cutMul (constCut 0 1) (constCut 0 1) = constCut 0 1 :=
  cutMul_zero_zero

/-- 1 × 1 = 1. -/
example : cutMul (constCut 1 1) (constCut 1 1) = constCut 1 1 :=
  cutMul_one_one

end E213.Math.Real213.CutMidSelf
