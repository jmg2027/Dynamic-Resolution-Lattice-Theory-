import E213.Research.Real213CutSum
import E213.Research.Real213CutSumTest

/-!
# Research.Real213CutBisection: bisection (cutHalf, cutMid) — IVT support

Half: c/2 ≤ m/k iff c ≤ 2m/k.
Mid: (x+y)/2 cut.

## 의의

IVT bisection algorithm 의 substrate.  Real213 위 의 root finding.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **cutHalf**: c/2 cut. -/
def cutHalf (c : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun m k => c (2*m) k

/-- **cutMid**: (cx+cy)/2 midpoint cut. -/
def cutMid (cx cy : Nat → Nat → Bool) : Nat → Nat → Bool :=
  cutHalf (cutSum cx cy)

end E213.Research.Real213CutSum

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- midpoint of (1, 1) is 1: cut at (1, 1) true. -/
example : cutMid (constCut 1 1) (constCut 1 1) 1 1 = true := by decide

/-- midpoint of (1, 1) is 1, NOT ≤ 0/1. -/
example : cutMid (constCut 1 1) (constCut 1 1) 0 1 = false := by decide

/-- midpoint of (0, 2) is 1, ≤ 1/1. -/
example : cutMid (constCut 0 1) (constCut 2 1) 1 1 = true := by decide

/-- cutHalf 의 idempotent-on-zero: 0/2 = 0. -/
example : cutHalf (constCut 0 1) 0 1 = true := by decide

/-- midpoint(1, 1) = 1 ≤ 1/1. -/
example : cutMid (constCut 1 1) (constCut 1 1) 1 1 = true := by decide

/-- midpoint(1, 1) = 1, NOT ≤ 0/1. -/
example : cutMid (constCut 1 1) (constCut 1 1) 0 1 = false := by decide

/-- midpoint(0, 4) = 2 ≤ 2/1. -/
example : cutMid (constCut 0 1) (constCut 4 1) 2 1 = true := by decide

/-- midpoint(0, 4) = 2, NOT ≤ 1/1. -/
example : cutMid (constCut 0 1) (constCut 4 1) 1 1 = false := by decide

/-- midpoint of equal cuts: cutMid c c uses cutHalf (cutSum c c). -/
theorem cutMid_def (cx cy : Nat → Nat → Bool) :
    cutMid cx cy = cutHalf (cutSum cx cy) := rfl

/-- cutHalf monotone in c. -/
theorem cutHalf_mono (c c' : Nat → Nat → Bool)
    (h : ∀ m' k', c m' k' = true → c' m' k' = true) (m k : Nat) :
    cutHalf c m k = true → cutHalf c' m k = true := fun hmk => h (2*m) k hmk

/-- **cutHalf (constCut a b) = constCut a (2*b)**: a/b / 2 = a/(2b). -/
theorem cutHalf_constCut (a b : Nat) :
    cutHalf (constCut a b) = constCut a (2*b) := by
  funext m k
  show decide (a*k ≤ b*(2*m)) = decide (a*k ≤ (2*b)*m)
  congr 1
  rw [← Nat.mul_assoc, Nat.mul_comm b 2]

end E213.Research.Real213CutSum
