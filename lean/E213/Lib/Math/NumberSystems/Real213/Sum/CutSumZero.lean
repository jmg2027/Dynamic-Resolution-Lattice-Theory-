import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulComm
import E213.Lib.Math.NumberSystems.Real213.Mul.CutAlgebraic
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
/-!
# CutSumZero: cutSum (zero) (zero) = zero

Specific algebraic identity: 0 + 0 = 0 at cut level.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Sum.CutSumZero

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection (cutHalf cutMid)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul cutMulOuter)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMulComm (cutMulOuter_eq_true_iff)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum cutSumAux)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm (cutSumAux_eq_true_iff)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutAlgebraic (constCut_zero_always)

/-- **cutSum 0 0 = 0** pointwise (∅-axiom).  Avoids `funext`. -/
theorem cutSum_zero_zero_at (m k : Nat) :
    cutSum (constCut 0 1) (constCut 0 1) m k = constCut 0 1 m k := by
  rw [constCut_zero_always]
  show cutSumAux (constCut 0 1) (constCut 0 1) k (2*m) (2*m) = true
  refine (cutSumAux_eq_true_iff _ _ _ _ _).mpr
    ⟨0, Nat.zero_le _, ?_, ?_⟩
  · exact constCut_zero_always 0 (2*k)
  · exact constCut_zero_always (2*m - 0) (2*k)

/-- **cutMul 0 0 = 0** pointwise (∅-axiom).  Avoids `funext`. -/
theorem cutMul_zero_zero_at (m k : Nat) :
    cutMul (constCut 0 1) (constCut 0 1) m k = constCut 0 1 m k := by
  rw [constCut_zero_always]
  show cutMulOuter (constCut 0 1) (constCut 0 1) k m ((m+1)*(k+1)) ((m+1)*(k+1))
       = true
  refine (cutMulOuter_eq_true_iff _ _ k m _ _).mpr
    ⟨0, Nat.zero_le _, 0, Nat.zero_le _, ?_, ?_, ?_⟩
  · exact constCut_zero_always 0 k
  · exact constCut_zero_always 0 k
  · rw [Nat.zero_mul]; exact Nat.zero_le _

-- DELETED: function-eq cutMul_zero_zero. Use cutMul_zero_zero_at.

/-- **cutHalf zero = zero** pointwise (∅-axiom). -/
theorem cutHalf_zero_at (m k : Nat) :
    cutHalf (constCut 0 1) m k = constCut 0 1 m k := by
  show constCut 0 1 (2*m) k = constCut 0 1 m k
  rw [constCut_zero_always, constCut_zero_always]

-- DELETED: function-eq cutHalf_zero. Use cutHalf_zero_at.

/-- **cutMid zero zero = zero** pointwise (∅-axiom). -/
theorem cutMid_zero_zero_at (m k : Nat) :
    cutMid (constCut 0 1) (constCut 0 1) m k = constCut 0 1 m k := by
  show cutHalf (cutSum (constCut 0 1) (constCut 0 1)) m k = constCut 0 1 m k
  show cutSum (constCut 0 1) (constCut 0 1) (2*m) k = constCut 0 1 m k
  rw [cutSum_zero_zero_at]
  rw [constCut_zero_always, constCut_zero_always]

-- DELETED: function-eq cutMid_zero_zero. Use cutMid_zero_zero_at.

/-- 1/2 + 1/2 = 1 at (1, 1) — concrete decide. -/
example : cutSum (constCut 1 2) (constCut 1 2) 1 1 = constCut 1 1 1 1 := by decide

/-- 1/2 + 1/2 = 1 at (2, 2) — also true. -/
example : cutSum (constCut 1 2) (constCut 1 2) 2 2 = constCut 1 1 2 2 := by decide

/-- 1/3 + 2/3 = 1 — at (3, 3) precision suffices. -/
example : cutSum (constCut 1 3) (constCut 2 3) 3 3 = true := by decide

/-- 2 + 3 = 5 ≤ 5/1. -/
example : cutSum (constCut 2 1) (constCut 3 1) 5 1 = true := by decide

/-- 2 * 3 = 6, NOT ≤ 5/1. -/
example : cutMul (constCut 2 1) (constCut 3 1) 5 1 = false := by decide

end E213.Lib.Math.NumberSystems.Real213.Sum.CutSumZero
