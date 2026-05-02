import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutSumOne
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutPoset

/-!
# Research.Real213CutDouble: 2x cut function

cutDouble c := "2x ≤ m/k" iff "x ≤ m/(2k)" → c m (2k).
-/

namespace E213.Math.Real213.CutDouble

open E213.Math.Real213.CutSum (cutSum cutSumAux)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutSumOne (cutSum_self)
open E213.Math.Real213.CutBisection (cutHalf cutHalf_constCut cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPoset (cutEq cutLe)
open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)

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

/-- cutSumAux for doubled cuts at precision k = cutSumAux for original
    cuts at precision (2k) — doubling acts on the inner k slot. -/
theorem cutSumAux_cutDouble (cx cy : Nat → Nat → Bool)
    (k m1Max : Nat) :
    ∀ n, cutSumAux (cutDouble cx) (cutDouble cy) k m1Max n
       = cutSumAux cx cy (2*k) m1Max n
  | 0 => rfl
  | n+1 => by
    show ((cx (n+1) (2*(2*k)) && cy (m1Max - (n+1)) (2*(2*k)))
          || cutSumAux (cutDouble cx) (cutDouble cy) k m1Max n)
       = ((cx (n+1) (2*(2*k)) && cy (m1Max - (n+1)) (2*(2*k)))
          || cutSumAux cx cy (2*k) m1Max n)
    rw [cutSumAux_cutDouble cx cy k m1Max n]

/-- **cutDouble distributes over cutSum**. -/
theorem cutDouble_cutSum (cx cy : Nat → Nat → Bool) :
    cutDouble (cutSum cx cy) = cutSum (cutDouble cx) (cutDouble cy) := by
  funext m k
  show cutSumAux cx cy (2*k) (2*m) (2*m)
     = cutSumAux (cutDouble cx) (cutDouble cy) k (2*m) (2*m)
  rw [cutSumAux_cutDouble]

/-- **cutDouble distributes over cutMid**.
    Composes cutDouble_cutSum with cutDouble_cutHalf_comm. -/
theorem cutDouble_cutMid (cx cy : Nat → Nat → Bool) :
    cutDouble (cutMid cx cy) = cutMid (cutDouble cx) (cutDouble cy) := by
  show cutDouble (cutHalf (cutSum cx cy))
     = cutHalf (cutSum (cutDouble cx) (cutDouble cy))
  rw [← cutDouble_cutSum]
  exact cutDouble_cutHalf_comm _

end E213.Math.Real213.CutDouble
