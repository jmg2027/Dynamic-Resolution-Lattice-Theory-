import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumTest

/-!
# CutMaxMin: cutMax / cutMin (trivial cut operations)

max(x, y) ≤ m/k iff x ≤ m/k AND y ≤ m/k → cut := cx ∧ cy.
min(x, y) ≤ m/k iff x ≤ m/k OR y ≤ m/k → cut := cx ∨ cy.

## Significance

213-native: expressed directly as Bool combinators without search.  A
*special form* of cutBinary — every (m1, m2) combination is trivially
determined.  Continuity is also trivially obvious.
-/

namespace E213.Math.Real213.CutMaxMin

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSumTest (constCut)

/-- **cutMax**: max cut. -/
def cutMax (cx cy : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun m k => cx m k && cy m k

/-- **cutMin**: min cut. -/
def cutMin (cx cy : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun m k => cx m k || cy m k

/-- max(1, 1) = 1: at (1, 1) true. -/
example : cutMax (constCut 1 1) (constCut 1 1) 1 1 = true := by decide

/-- max(1, 2) = 2 ≤ 2/1 true, NOT ≤ 1/1. -/
example : cutMax (constCut 1 1) (constCut 2 1) 2 1 = true := by decide
example : cutMax (constCut 1 1) (constCut 2 1) 1 1 = false := by decide

/-- min(1, 2) = 1 ≤ 1/1 true. -/
example : cutMin (constCut 1 1) (constCut 2 1) 1 1 = true := by decide

/-- commutativity of min, pointwise (PURE). -/
theorem cutMin_comm_at (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutMin cx cy m k = cutMin cy cx m k := by
  show (cx m k || cy m k) = (cy m k || cx m k)
  cases cx m k <;> cases cy m k <;> rfl

theorem cutMin_comm (cx cy : Nat → Nat → Bool) :
    ∀ m k, cutMin cx cy m k = cutMin cy cx m k :=
  cutMin_comm_at cx cy

/-- commutativity of max, pointwise (PURE). -/
theorem cutMax_comm_at (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutMax cx cy m k = cutMax cy cx m k := by
  show (cx m k && cy m k) = (cy m k && cx m k)
  cases cx m k <;> cases cy m k <;> rfl

theorem cutMax_comm (cx cy : Nat → Nat → Bool) :
    ∀ m k, cutMax cx cy m k = cutMax cy cx m k :=
  cutMax_comm_at cx cy

/-- associativity of max, pointwise (PURE). -/
theorem cutMax_assoc_at (cx cy cz : Nat → Nat → Bool) (m k : Nat) :
    cutMax (cutMax cx cy) cz m k = cutMax cx (cutMax cy cz) m k := by
  show ((cx m k && cy m k) && cz m k) = (cx m k && (cy m k && cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

theorem cutMax_assoc (cx cy cz : Nat → Nat → Bool) :
    ∀ m k, cutMax (cutMax cx cy) cz m k = cutMax cx (cutMax cy cz) m k :=
  cutMax_assoc_at cx cy cz

/-- associativity of min, pointwise (PURE). -/
theorem cutMin_assoc_at (cx cy cz : Nat → Nat → Bool) (m k : Nat) :
    cutMin (cutMin cx cy) cz m k = cutMin cx (cutMin cy cz) m k := by
  show ((cx m k || cy m k) || cz m k) = (cx m k || (cy m k || cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

theorem cutMin_assoc (cx cy cz : Nat → Nat → Bool) :
    ∀ m k, cutMin (cutMin cx cy) cz m k = cutMin cx (cutMin cy cz) m k :=
  cutMin_assoc_at cx cy cz

end E213.Math.Real213.CutMaxMin
