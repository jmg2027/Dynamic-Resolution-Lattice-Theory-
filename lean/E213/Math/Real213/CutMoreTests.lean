import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumTest

/-!
# Research.Real213CutMoreTests: additional concrete decide tests

Cut-level verification of various rational arithmetic.
-/

namespace E213.Math.Real213.CutMoreTests

open E213.Firmware E213.Hypervisor

/-- 1 + 1 + 1 = 3 ≤ 3/1. -/
example : cutSum (cutSum (constCut 1 1) (constCut 1 1)) (constCut 1 1) 3 1 = true
  := by decide

/-- 1 * 1 * 1 = 1 ≤ 1/1. -/
example : cutMul (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1) 1 1 = true
  := by decide

/-- 1*1*1 NOT ≤ 0/1. -/
example : cutMul (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1) 0 1 = false
  := by decide

/-- 0 + 1 + 2 = 3 ≤ 3/1. -/
example : cutSum (cutSum (constCut 0 1) (constCut 1 1)) (constCut 2 1) 3 1 = true
  := by decide

/-- 1 + 0 = 1, NOT ≤ 0/1. -/
example : cutSum (constCut 1 1) (constCut 0 1) 0 1 = false := by decide

/-- 1 * 0 = 0 ≤ 0/1. -/
example : cutMul (constCut 1 1) (constCut 0 1) 0 1 = true := by decide

/-- cutSum (1)(1) at (2, 1) = constCut 2 1 — both true. -/
example : cutSum (constCut 1 1) (constCut 1 1) 2 1
        = constCut 2 1 2 1 := by decide

/-- cutSum (1)(1) at (1, 1) = constCut 2 1 — both false. -/
example : cutSum (constCut 1 1) (constCut 1 1) 1 1
        = constCut 2 1 1 1 := by decide

/-- cutMul (1)(1) at (1, 1) = constCut 1 1 — both true. -/
example : cutMul (constCut 1 1) (constCut 1 1) 1 1
        = constCut 1 1 1 1 := by decide

/-- cutMul (1)(1) at (0, 1) = constCut 1 1 — both false. -/
example : cutMul (constCut 1 1) (constCut 1 1) 0 1
        = constCut 1 1 0 1 := by decide

/-- cutSum associativity at (3, 1): (1+1)+1 = 1+(1+1) = 3.  Both true. -/
example : cutSum (cutSum (constCut 1 1) (constCut 1 1)) (constCut 1 1) 3 1
        = cutSum (constCut 1 1) (cutSum (constCut 1 1) (constCut 1 1)) 3 1
  := by decide

/-- cutSum associativity at (2, 1): (1+1)+1=3, NOT ≤ 2.  Both false. -/
example : cutSum (cutSum (constCut 1 1) (constCut 1 1)) (constCut 1 1) 2 1
        = cutSum (constCut 1 1) (cutSum (constCut 1 1) (constCut 1 1)) 2 1
  := by decide

/-- cutMul associativity at (1, 1): (1*1)*1=1*(1*1)=1.  Both true. -/
example : cutMul (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1) 1 1
        = cutMul (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1)) 1 1
  := by decide

end E213.Math.Real213.CutMoreTests
