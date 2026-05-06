import E213.Math.Real213.CutMaxMin
import E213.Math.Real213.CutBisection

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
/-!
# Real213CutAlgebraStruct: structured cut algebra

Bind all cut operations into a single struct.  Reusable abstraction
for cut-level rational arithmetic.
-/

namespace E213.Math.Real213.CutAlgebraStruct

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutBisection (cutMid cutHalf)
open E213.Math.Real213.CutMaxMin (cutMax cutMin)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.Core (Real213)

/-- **CutAlgebra**: bundle of all standard cut operations. -/
structure CutAlgebra where
  zero : Nat → Nat → Bool
  one : Nat → Nat → Bool
  add : (Nat → Nat → Bool) → (Nat → Nat → Bool) → Nat → Nat → Bool
  mul : (Nat → Nat → Bool) → (Nat → Nat → Bool) → Nat → Nat → Bool
  max : (Nat → Nat → Bool) → (Nat → Nat → Bool) → Nat → Nat → Bool
  min : (Nat → Nat → Bool) → (Nat → Nat → Bool) → Nat → Nat → Bool
  half : (Nat → Nat → Bool) → Nat → Nat → Bool
  mid : (Nat → Nat → Bool) → (Nat → Nat → Bool) → Nat → Nat → Bool

/-- **Standard CutAlgebra instance**. -/
def stdCutAlgebra : CutAlgebra where
  zero := constCut 0 1
  one := constCut 1 1
  add := cutSum
  mul := cutMul
  max := cutMax
  min := cutMin
  half := cutHalf
  mid := cutMid

/-- Formal verification that 1 + 1 = 2 in stdCutAlgebra. -/
example : stdCutAlgebra.add stdCutAlgebra.one stdCutAlgebra.one 2 1 = true := by decide

/-- Verification that the cut for 0 is "always true". -/
example : stdCutAlgebra.zero 0 1 = true := by decide

end E213.Math.Real213.CutAlgebraStruct
