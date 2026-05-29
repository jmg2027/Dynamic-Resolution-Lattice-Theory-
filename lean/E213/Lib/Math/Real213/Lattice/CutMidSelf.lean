import E213.Meta.Tactic.BoolHelper
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.Real213.Sum.CutSumOne
import E213.Lib.Math.Real213.Mul.ConstCutScale
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Lib.Math.Real213.Sum.CutSumZero

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Core.CutPoset
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# CutMidSelf: midpoint(c, c) = c for const cut

cutMid (constCut a b) (constCut a b) = constCut a b for b ≥ 1.

Via cutSum_self + cutHalf_constCut + constCut_scale.
-/

namespace E213.Lib.Math.Real213.Lattice.CutMidSelf

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutHalf cutHalf_constCut cutHalf_constCut_at cutMid)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSumOne (cutSum_self cutSum_self_at)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Mul.ConstCutScale (constCut_scale constCut_scale_at)
open E213.Lib.Math.Real213.Sum.CutSumOne
  (cutSum_half_general cutSum_int_int cutSum_int_half cutSum_half_int)
open E213.Lib.Math.Real213.Mul.CutMulOne (cutMul_one_const_at cutMul_const_one_at cutMul_one_one_at)
open E213.Lib.Math.Real213.Sum.CutSumZero (cutMul_zero_zero_at)

open E213.Tactic.BoolHelper (bool_eq_iff)

/-- **midpoint(c, c) = c** for c = a/b — pointwise (∅-axiom). -/
theorem cutMid_self_constCut_at (a b m k : Nat) (_hb : b ≥ 1) :
    cutMid (constCut a b) (constCut a b) m k = constCut a b m k := by
  show cutHalf (cutSum (constCut a b) (constCut a b)) m k = constCut a b m k
  show cutSum (constCut a b) (constCut a b) (2*m) k = constCut a b m k
  rw [cutSum_self_at]
  -- Goal: constCut (2*a) b (2*m) k = constCut a b m k
  -- = decide ((2*a)*k ≤ b*(2*m)) = decide (a*k ≤ b*m)
  apply bool_eq_iff
  constructor
  · intro h
    have h1 : (2*a)*k ≤ b*(2*m) := of_decide_eq_true h
    have h2 : 2*(a*k) ≤ 2*(b*m) := by
      rw [E213.Tactic.NatHelper.mul_assoc] at h1
      rw [show b*(2*m) = 2*(b*m) from by
        rw [E213.Tactic.NatHelper.mul_left_comm]] at h1
      exact h1
    exact decide_eq_true
      (Nat.le_of_mul_le_mul_left h2 (Nat.zero_lt_succ 1))
  · intro h
    have h1 : a*k ≤ b*m := of_decide_eq_true h
    have h2 : 2*(a*k) ≤ 2*(b*m) := Nat.mul_le_mul_left 2 h1
    apply decide_eq_true
    rw [E213.Tactic.NatHelper.mul_assoc, show b*(2*m) = 2*(b*m) from by
      rw [E213.Tactic.NatHelper.mul_left_comm]]
    exact h2

-- DELETED: function-eq cutMid_self_constCut. Use cutMid_self_constCut_at.

/-- **midpoint(a/2, c/2) ≡ (a+c)/4** (cutEq, PURE). -/
theorem cutMid_half_general (a c : Nat) :
    E213.Lib.Math.Real213.Core.CutPoset.cutEq
      (cutMid (constCut a 2) (constCut c 2)) (constCut (a+c) 4) := by
  intro m k
  show cutHalf (cutSum (constCut a 2) (constCut c 2)) m k = constCut (a+c) 4 m k
  show cutSum (constCut a 2) (constCut c 2) (2*m) k = constCut (a+c) 4 m k
  rw [cutSum_half_general a c (2*m) k]
  show constCut (a+c) 2 (2*m) k = constCut (a+c) 4 m k
  show decide ((a+c) * k ≤ 2 * (2*m)) = decide ((a+c) * k ≤ 4 * m)
  congr 2
  rw [← E213.Tactic.NatHelper.mul_assoc]

/-- **midpoint(a/1, c/1) ≡ (a+c)/2** (cutEq, PURE). -/
theorem cutMid_int_int (a c : Nat) :
    E213.Lib.Math.Real213.Core.CutPoset.cutEq
      (cutMid (constCut a 1) (constCut c 1)) (constCut (a+c) 2) := by
  intro m k
  show cutHalf (cutSum (constCut a 1) (constCut c 1)) m k = constCut (a+c) 2 m k
  show cutSum (constCut a 1) (constCut c 1) (2*m) k = constCut (a+c) 2 m k
  rw [cutSum_int_int a c (2*m) k]
  show decide ((a+c) * k ≤ 1 * (2*m)) = decide ((a+c) * k ≤ 2 * m)
  rw [Nat.one_mul]

/-- **midpoint(a/1, c/2) ≡ (2a+c)/4** (cutEq, PURE). -/
theorem cutMid_int_half (a c : Nat) :
    E213.Lib.Math.Real213.Core.CutPoset.cutEq
      (cutMid (constCut a 1) (constCut c 2)) (constCut (2*a+c) 4) := by
  intro m k
  show cutHalf (cutSum (constCut a 1) (constCut c 2)) m k = constCut (2*a+c) 4 m k
  show cutSum (constCut a 1) (constCut c 2) (2*m) k = constCut (2*a+c) 4 m k
  rw [cutSum_int_half a c (2*m) k]
  show decide ((2*a+c) * k ≤ 2 * (2*m)) = decide ((2*a+c) * k ≤ 4 * m)
  congr 2
  rw [← E213.Tactic.NatHelper.mul_assoc]

/-- **midpoint(a/2, c/1) ≡ (a+2c)/4** (cutEq, PURE). -/
theorem cutMid_half_int (a c : Nat) :
    E213.Lib.Math.Real213.Core.CutPoset.cutEq
      (cutMid (constCut a 2) (constCut c 1)) (constCut (a+2*c) 4) := by
  intro m k
  show cutHalf (cutSum (constCut a 2) (constCut c 1)) m k = constCut (a+2*c) 4 m k
  show cutSum (constCut a 2) (constCut c 1) (2*m) k = constCut (a+2*c) 4 m k
  rw [cutSum_half_int a c (2*m) k]
  show decide ((a+2*c) * k ≤ 2 * (2*m)) = decide ((a+2*c) * k ≤ 4 * m)
  congr 2
  rw [← E213.Tactic.NatHelper.mul_assoc]

/-! ### Concrete cutMid evaluations on integer pairs (cutEq, PURE) -/

/-- midpoint(0, 1) ≡ 1/2. -/
example : E213.Lib.Math.Real213.Core.CutPoset.cutEq
    (cutMid (constCut 0 1) (constCut 1 1)) (constCut 1 2) :=
  cutMid_int_int 0 1

/-- midpoint(0, 4) ≡ 2. -/
example : E213.Lib.Math.Real213.Core.CutPoset.cutEq
    (cutMid (constCut 0 1) (constCut 4 1)) (constCut 4 2) :=
  cutMid_int_int 0 4

/-- midpoint(1, 3) ≡ 2. -/
example : E213.Lib.Math.Real213.Core.CutPoset.cutEq
    (cutMid (constCut 1 1) (constCut 3 1)) (constCut 4 2) :=
  cutMid_int_int 1 3

/-- midpoint(2, 8) ≡ 5. -/
example : E213.Lib.Math.Real213.Core.CutPoset.cutEq
    (cutMid (constCut 2 1) (constCut 8 1)) (constCut 10 2) :=
  cutMid_int_int 2 8

/-! ### Y2: cutMul concrete applications (pointwise PURE) -/

/-- 1 × (5/7) = 5/7 pointwise. -/
example (m k : Nat) :
    cutMul (constCut 1 1) (constCut 5 7) m k = constCut 5 7 m k :=
  cutMul_one_const_at 5 7 m k

/-- (3/4) × 1 = 3/4 pointwise. -/
example (m k : Nat) :
    cutMul (constCut 3 4) (constCut 1 1) m k = constCut 3 4 m k :=
  cutMul_const_one_at 3 4 m k

/-- 0 × 0 = 0 pointwise. -/
example (m k : Nat) :
    cutMul (constCut 0 1) (constCut 0 1) m k = constCut 0 1 m k :=
  cutMul_zero_zero_at m k

/-- 1 × 1 = 1 pointwise. -/
example (m k : Nat) :
    cutMul (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k :=
  cutMul_one_one_at m k

end E213.Lib.Math.Real213.Lattice.CutMidSelf
