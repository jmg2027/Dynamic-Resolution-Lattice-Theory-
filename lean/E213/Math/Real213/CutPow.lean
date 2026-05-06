import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumTest

/-!
# CutPow: cut-level powers + polynomial building blocks

x^n via repeated cutMul.

## Definition

cutPow x n := x^n cut.
cutScale a b cx := (a/b) * cx.
-/

namespace E213.Math.Real213.CutPow

open E213.Theory E213.Lens
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutMul (cutMul)

/-- **cutPow**: x^n via repeated cutMul. -/
def cutPow (x : Nat → Nat → Bool) : Nat → Nat → Nat → Bool
  | 0 => constCut 1 1
  | n+1 => cutMul (cutPow x n) x

/-- **cutScale**: a/b * cx via cutMul with const. -/
def cutScale (a b : Nat) (cx : Nat → Nat → Bool) : Nat → Nat → Bool :=
  cutMul (constCut a b) cx

/-- 1^0 = 1 ≤ 1/1. -/
example : cutPow (constCut 1 1) 0 1 1 = true := by decide

/-- 1^1 = 1 ≤ 1/1. -/
example : cutPow (constCut 1 1) 1 1 1 = true := by decide

/-- 1^2 = 1 ≤ 1/1. -/
example : cutPow (constCut 1 1) 2 1 1 = true := by decide

/-- (2/1)^2 = 4 ≤ 4/1.  Note: cutMul precision boundary applies — verifiable
    only at exact upper boundary. -/
example : cutPow (constCut 2 1) 2 4 1 = true := by decide

/-- x^0 = 1 (definitional). -/
theorem cutPow_zero (x : Nat → Nat → Bool) : cutPow x 0 = constCut 1 1 := rfl

/-- x^(n+1) = (x^n) * x (definitional). -/
theorem cutPow_succ (x : Nat → Nat → Bool) (n : Nat) :
    cutPow x (n+1) = cutMul (cutPow x n) x := rfl

end E213.Math.Real213.CutPow
