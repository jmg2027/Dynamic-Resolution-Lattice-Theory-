import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumTest

/-!
# Research.Real213CutInv: cut-level reciprocal + division

For positive c (c > 0): 1/c is well-defined.

cutInv c m k = "1/c ≤ m/k" via "c > k/m" (strict).
Note: at exact rational boundary "c = k/m", returns false (lower bound).
-/

namespace E213.Math.Real213.CutInv

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.Core (Real213)

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
    Note: when combining cutMul + cutInv, a boundary precision artifact occurs;
    "x/y ≤ exact ratio" is only captured with strict criteria.  Finer
    precision redesign is separate. -/
def cutDiv (cx cy : Nat → Nat → Bool) : Nat → Nat → Bool :=
  cutMul cx (cutInv cy)

/-- **cutInv (cutInv c) = c**: double inverse is identity. -/
theorem cutInv_cutInv (c : Nat → Nat → Bool) :
    cutInv (cutInv c) = c := by
  funext m k
  show Bool.not (Bool.not (c m k)) = c m k
  cases c m k
  · rfl
  · rfl

end E213.Math.Real213.CutInv
