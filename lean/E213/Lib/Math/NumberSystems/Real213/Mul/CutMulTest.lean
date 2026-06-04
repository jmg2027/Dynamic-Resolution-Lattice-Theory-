import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest

import E213.Lib.Math.NumberSystems.Real213.Core.Core
/-!
# CutMulTest: cutMul verification on rational products

Accuracy verification of cutMul from `Real213CutMul.lean` on const cuts (rationals).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mul.CutMulTest

open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)

/-- 1 * 1 = 1 ≤ 1/1 = true. -/
example : cutMul (constCut 1 1) (constCut 1 1) 1 1 = true := by decide

/-- 1 * 1 = 1, but ≤ 0/1 = false. -/
example : cutMul (constCut 1 1) (constCut 1 1) 0 1 = false := by decide

/-- (1/2) * (1/2) = 1/4 ≤ 1/4 = true. -/
example : cutMul (constCut 1 2) (constCut 1 2) 1 4 = true := by decide

/-- (1/2) * (1/2) = 1/4, NOT ≤ 1/5. -/
example : cutMul (constCut 1 2) (constCut 1 2) 1 5 = false := by decide

/-- (1/2) * (1/3) = 1/6 ≤ 1/6 = true. -/
example : cutMul (constCut 1 2) (constCut 1 3) 1 6 = true := by decide

/-- 2 * 3 = 6 ≤ 6/1 = true. -/
example : cutMul (constCut 2 1) (constCut 3 1) 6 1 = true := by decide

/-- 2 * 3 = 6, NOT ≤ 5/1. -/
example : cutMul (constCut 2 1) (constCut 3 1) 5 1 = false := by decide

end E213.Lib.Math.NumberSystems.Real213.Mul.CutMulTest
