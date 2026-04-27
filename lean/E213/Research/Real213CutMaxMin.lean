import E213.Research.Real213CutMul
import E213.Research.Real213CutSumTest

/-!
# Research.Real213CutMaxMin: cutMax / cutMin (trivial cut operations)

max(x, y) ≤ m/k iff x ≤ m/k AND y ≤ m/k → cut := cx ∧ cy.
min(x, y) ≤ m/k iff x ≤ m/k OR y ≤ m/k → cut := cx ∨ cy.

## 의의

213-native: 검색 없 이 직접 Bool combinator 로 표현.  cutBinary 의
*특수 form* — 모든 (m1, m2) 조합 이 trivial 하 게 결정.  Continuity
도 자명.
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

/-- min 의 commutativity. -/
theorem cutMin_comm (cx cy : Nat → Nat → Bool) :
    cutMin cx cy = cutMin cy cx := by
  funext m k
  show (cx m k || cy m k) = (cy m k || cx m k)
  cases cx m k <;> cases cy m k <;> rfl

/-- max 의 commutativity. -/
theorem cutMax_comm (cx cy : Nat → Nat → Bool) :
    cutMax cx cy = cutMax cy cx := by
  funext m k
  show (cx m k && cy m k) = (cy m k && cx m k)
  cases cx m k <;> cases cy m k <;> rfl

/-- max 의 associativity. -/
theorem cutMax_assoc (cx cy cz : Nat → Nat → Bool) :
    cutMax (cutMax cx cy) cz = cutMax cx (cutMax cy cz) := by
  funext m k
  show ((cx m k && cy m k) && cz m k) = (cx m k && (cy m k && cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

/-- min 의 associativity. -/
theorem cutMin_assoc (cx cy cz : Nat → Nat → Bool) :
    cutMin (cutMin cx cy) cz = cutMin cx (cutMin cy cz) := by
  funext m k
  show ((cx m k || cy m k) || cz m k) = (cx m k || (cy m k || cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

end E213.Research.Real213CutSum
