import E213.Research.Real213CutMul
import E213.Research.Real213CutSumTest

/-!
# Research.Real213CutMaxMin: cutMax / cutMin (trivial cut operations)

max(x, y) ≤ m/k iff x ≤ m/k AND y ≤ m/k → cut := cx ∧ cy.
min(x, y) ≤ m/k iff x ≤ m/k OR y ≤ m/k → cut := cx ∨ cy.

## Significance

213-native: expressed directly as Bool combinators without search.  A
*special form* of cutBinary — every (m1, m2) combination is trivially
determined.  Continuity is also trivially obvious.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

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

/-- commutativity of min. -/
theorem cutMin_comm (cx cy : Nat → Nat → Bool) :
    cutMin cx cy = cutMin cy cx := by
  funext m k
  show (cx m k || cy m k) = (cy m k || cx m k)
  cases cx m k <;> cases cy m k <;> rfl

/-- commutativity of max. -/
theorem cutMax_comm (cx cy : Nat → Nat → Bool) :
    cutMax cx cy = cutMax cy cx := by
  funext m k
  show (cx m k && cy m k) = (cy m k && cx m k)
  cases cx m k <;> cases cy m k <;> rfl

/-- associativity of max. -/
theorem cutMax_assoc (cx cy cz : Nat → Nat → Bool) :
    cutMax (cutMax cx cy) cz = cutMax cx (cutMax cy cz) := by
  funext m k
  show ((cx m k && cy m k) && cz m k) = (cx m k && (cy m k && cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

/-- associativity of min. -/
theorem cutMin_assoc (cx cy cz : Nat → Nat → Bool) :
    cutMin (cutMin cx cy) cz = cutMin cx (cutMin cy cz) := by
  funext m k
  show ((cx m k || cy m k) || cz m k) = (cx m k || (cy m k || cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

end E213.Research.Real213CutSum
