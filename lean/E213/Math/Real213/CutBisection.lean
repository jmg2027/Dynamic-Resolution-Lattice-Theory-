import E213.Kernel.Tactic.Nat213
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest

/-!
# CutBisection: bisection (cutHalf, cutMid) — IVT support

Half: c/2 ≤ m/k iff c ≤ 2m/k.
Mid: (x+y)/2 cut.

## Significance

Substrate of the IVT bisection algorithm.  Root finding on Real213.
-/

namespace E213.Math.Real213.CutBisection

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor

/-- **cutHalf**: c/2 cut. -/
def cutHalf (c : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun m k => c (2*m) k

/-- **cutMid**: (cx+cy)/2 midpoint cut. -/
def cutMid (cx cy : Nat → Nat → Bool) : Nat → Nat → Bool :=
  cutHalf (cutSum cx cy)

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)

/-- midpoint of (1, 1) is 1: cut at (1, 1) true. -/
example : cutMid (constCut 1 1) (constCut 1 1) 1 1 = true := by decide

/-- midpoint of (1, 1) is 1, NOT ≤ 0/1. -/
example : cutMid (constCut 1 1) (constCut 1 1) 0 1 = false := by decide

/-- midpoint of (0, 2) is 1, ≤ 1/1. -/
example : cutMid (constCut 0 1) (constCut 2 1) 1 1 = true := by decide

/-- cutHalf idempotent-on-zero: 0/2 = 0. -/
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

/-- **cutHalf (constCut a b) m k = constCut a (2*b) m k** pointwise (∅-axiom). -/
theorem cutHalf_constCut_at (a b m k : Nat) :
    cutHalf (constCut a b) m k = constCut a (2*b) m k := by
  show decide (a*k ≤ b*(2*m)) = decide (a*k ≤ (2*b)*m)
  congr 1
  rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b 2]

/-- **cutHalf (constCut a b) ≡ constCut a (2*b)** (cutEq, PURE):
    a/b / 2 ≡ a/(2b) pointwise. -/
theorem cutHalf_constCut (a b : Nat) :
    ∀ m k, cutHalf (constCut a b) m k = constCut a (2*b) m k :=
  cutHalf_constCut_at a b

end E213.Math.Real213.CutBisection
