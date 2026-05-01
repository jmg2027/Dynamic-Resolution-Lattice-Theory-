import E213.Research.Real213.CutPow
import E213.Research.Real213.CutMulOne
import E213.Research.Real213.CutSumZero

/-!
# Research.Real213CutPowConst: cutPow on const cuts

cutPow (constCut a b) 0 = 1, cutPow (constCut a b) 1 = (constCut a b).
-/

namespace E213.Research.Real213.CutPowConst

open E213.Firmware E213.Hypervisor

/-- (a/b)^1 = a/b for any a, b. -/
theorem cutPow_one_const (a b : Nat) :
    cutPow (constCut a b) 1 = constCut a b := cutMul_one_const a b

/-- **0^(n+1) = 0** for cut zero. -/
theorem cutPow_zero_succ (n : Nat) :
    cutPow (constCut 0 1) (n+1) = constCut 0 1 := by
  induction n with
  | zero =>
    show cutMul (cutPow (constCut 0 1) 0) (constCut 0 1) = constCut 0 1
    show cutMul (constCut 1 1) (constCut 0 1) = constCut 0 1
    exact cutMul_one_const 0 1
  | succ k ih =>
    show cutMul (cutPow (constCut 0 1) (k+1)) (constCut 0 1) = constCut 0 1
    rw [ih]
    exact cutMul_zero_zero

/-- **1^n = 1** for any n. -/
theorem cutPow_one_n (n : Nat) :
    cutPow (constCut 1 1) n = constCut 1 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show cutMul (cutPow (constCut 1 1) k) (constCut 1 1) = constCut 1 1
    rw [ih]
    exact cutMul_one_one

end E213.Research.Real213.CutPowConst
