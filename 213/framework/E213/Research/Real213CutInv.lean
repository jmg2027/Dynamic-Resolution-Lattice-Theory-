import E213.Research.Real213CutMul
import E213.Research.Real213CutSumTest

/-!
# Research.Real213CutInv: cut-level reciprocal + division

For positive c (c > 0): 1/c is well-defined.

cutInv c m k = "1/c ≤ m/k" via "c > k/m" (strict).
Note: at exact rational boundary "c = k/m", returns false (lower bound).
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **cutInv** (lower-bound form): "1/c < m/k" via "c > k/m".
    Misses exact boundary "1/c = m/k" — for strict inequality only. -/
def cutInv (c : Nat → Nat → Bool) (m k : Nat) : Bool := !(c k m)

/-- 1/(1/2) = 2 < 3/1 (strict). -/
example : cutInv (constCut 1 2) 3 1 = true := by decide

/-- 1/(1/2) = 2, NOT < 1/1. -/
example : cutInv (constCut 1 2) 1 1 = false := by decide

/-- 1/(1/3) = 3 < 4/1. -/
example : cutInv (constCut 1 3) 4 1 = true := by decide

/-- **cutDiv**: division via reciprocal.
    Note: cutMul + cutInv combine 시 boundary precision artifact 발생,
    "x/y ≤ exact ratio" 가 strict 기 준 으 로 만 capture.  Finer
    precision redesign 별 도. -/
def cutDiv (cx cy : Nat → Nat → Bool) : Nat → Nat → Bool :=
  cutMul cx (cutInv cy)

end E213.Research.Real213CutSum
