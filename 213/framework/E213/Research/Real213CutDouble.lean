import E213.Research.Real213CutSum
import E213.Research.Real213CutSumTest
import E213.Research.Real213CutSumOne

/-!
# Research.Real213CutDouble: 2x cut function

cutDouble c := "2x ≤ m/k" iff "x ≤ m/(2k)" → c m (2k).
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **cutDouble**: 2x cut. -/
def cutDouble (c : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun m k => c m (2*k)

/-- cutDouble of const = const with doubled numerator. -/
theorem cutDouble_constCut (a b : Nat) :
    cutDouble (constCut a b) = constCut (2*a) b := by
  funext m k
  show decide (a * (2*k) ≤ b * m) = decide (2 * a * k ≤ b * m)
  rw [← Nat.mul_assoc, Nat.mul_comm a 2]

/-- 2 * (1/2) = 1: cutDouble (1/2) = constCut 2 2.  Cut-equivalent to 1. -/
example : cutDouble (constCut 1 2) = constCut 2 2 := cutDouble_constCut 1 2

/-- cutDouble of zero = zero. -/
theorem cutDouble_zero : cutDouble (constCut 0 1) = constCut 0 1 := by
  rw [cutDouble_constCut]

/-- cutDouble of cutDouble = quadruple: c m (4k). -/
theorem cutDouble_cutDouble (c : Nat → Nat → Bool) :
    cutDouble (cutDouble c) = (fun m k => c m (4*k)) := by
  funext m k
  show c m (2*(2*k)) = c m (4*k)
  congr 1
  rw [← Nat.mul_assoc]

/-- **cutSum c c = cutDouble c** for c = constCut a b. -/
theorem cutSum_self_eq_cutDouble (a b : Nat) :
    cutSum (constCut a b) (constCut a b) = cutDouble (constCut a b) := by
  rw [cutSum_self, cutDouble_constCut]

end E213.Research.Real213CutSum
