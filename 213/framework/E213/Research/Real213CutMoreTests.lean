import E213.Research.Real213CutMul
import E213.Research.Real213CutSumTest

/-!
# Research.Real213CutMoreTests: 추 가 concrete decide tests

다 양 한 rational arithmetic 의 cut-level 검증.
-/

namespace E213.Research.Real213CutSum

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

end E213.Research.Real213CutSum
