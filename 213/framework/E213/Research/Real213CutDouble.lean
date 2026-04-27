import E213.Research.Real213CutSum
import E213.Research.Real213CutSumTest
import E213.Research.Real213CutSumOne
import E213.Research.Real213CutBisection
import E213.Research.Real213CutPoset

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

/-- **cutDouble and cutHalf commute** universally. -/
theorem cutDouble_cutHalf_comm (c : Nat → Nat → Bool) :
    cutDouble (cutHalf c) = cutHalf (cutDouble c) := rfl

/-- **cutHalf (cutHalf (a/b)) = a/(4b)**: half of half is quarter. -/
theorem cutHalf_cutHalf_constCut (a b : Nat) :
    cutHalf (cutHalf (constCut a b)) = constCut a (4*b) := by
  rw [cutHalf_constCut, cutHalf_constCut]
  congr 1
  rw [← Nat.mul_assoc]

/-- **cutDouble (cutDouble (a/b)) = (4a)/b**: double-double quadruples. -/
theorem cutDouble_cutDouble_constCut (a b : Nat) :
    cutDouble (cutDouble (constCut a b)) = constCut (4*a) b := by
  rw [cutDouble_constCut, cutDouble_constCut]
  congr 1
  rw [← Nat.mul_assoc]

/-- cutDouble preserves cutEq. -/
theorem cutDouble_cutEq (cx cy : Nat → Nat → Bool)
    (h : cutEq cx cy) : cutEq (cutDouble cx) (cutDouble cy) :=
  fun m k => h m (2*k)

/-- cutDouble preserves cutLe. -/
theorem cutDouble_cutLe (cx cy : Nat → Nat → Bool)
    (h : cutLe cx cy) : cutLe (cutDouble cx) (cutDouble cy) :=
  fun m k => h m (2*k)

/-- cutHalf preserves cutEq. -/
theorem cutHalf_cutEq (cx cy : Nat → Nat → Bool)
    (h : cutEq cx cy) : cutEq (cutHalf cx) (cutHalf cy) :=
  fun m k => h (2*m) k

/-- cutHalf preserves cutLe. -/
theorem cutHalf_cutLe (cx cy : Nat → Nat → Bool)
    (h : cutLe cx cy) : cutLe (cutHalf cx) (cutHalf cy) :=
  fun m k => h (2*m) k

end E213.Research.Real213CutSum
