import E213.Research.Real213CutMaxMin
import E213.Research.Real213CutBisection

/-!
# Research.Real213CutAlgebraStruct: structured cut algebra

Bind all cut operations into a single struct.  Reusable abstraction
for cut-level rational arithmetic.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **CutAlgebra**: 모든 standard cut operation 의 binding. -/
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

/-- 1 + 1 = 2 의 stdCutAlgebra 형 식 verification. -/
example : stdCutAlgebra.add stdCutAlgebra.one stdCutAlgebra.one 2 1 = true := by decide

/-- 0 의 cut "always true" verification. -/
example : stdCutAlgebra.zero 0 1 = true := by decide

end E213.Research.Real213CutSum
