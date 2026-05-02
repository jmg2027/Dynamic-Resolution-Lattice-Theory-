import E213.Math.Real213.CutSum

/-!
# Research.Real213CutSumTest: concrete verification of cutSum on rationals

Accuracy verification of cutSum from `Real213CutSum.lean` on
*constant cuts* (rational reals).

Each const cut has the form `fun m k => decide(a*k ≤ b*m)` —
Dedekind cut for ratio a/b.  Sum a/b + a'/b' = (a*b' + a'*b)/(b*b').

## Verified cases

- 1 + 1 = 2 (constCut(1,1) ⊕ constCut(1,1) at various (m, k))
- 1/2 + 1/2 = 1
- 1/2 + 1/3 = 5/6
-/

namespace E213.Math.Real213.CutSumTest

open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.Core (Real213)

/-- Const cut for ratio a/b. -/
def constCut (a b : Nat) : Nat → Nat → Bool :=
  fun m k => decide (a * k ≤ b * m)

/-- 1 + 1 = 2: cutSum at (4, 1) = "2 ≤ 4/1" = true. -/
example : cutSum (constCut 1 1) (constCut 1 1) 4 1 = true := by decide

/-- 1 + 1 = 2: cutSum at (1, 1) = "2 ≤ 1/1" = false. -/
example : cutSum (constCut 1 1) (constCut 1 1) 1 1 = false := by decide

/-- 1 + 1 = 2: cutSum at (2, 1) = "2 ≤ 2/1" = true. -/
example : cutSum (constCut 1 1) (constCut 1 1) 2 1 = true := by decide

/-- 1/2 + 1/2 = 1: cutSum at (1, 1) = "1 ≤ 1/1" = true. -/
example : cutSum (constCut 1 2) (constCut 1 2) 1 1 = true := by decide

/-- 1/2 + 1/2 = 1: cutSum at (1, 2) = "1 ≤ 1/2" = false. -/
example : cutSum (constCut 1 2) (constCut 1 2) 1 2 = false := by decide

/-- 1/2 + 1/3 = 5/6: cutSum at (1, 1) = "5/6 ≤ 1" = true. -/
example : cutSum (constCut 1 2) (constCut 1 3) 1 1 = true := by decide

/-- 1/2 + 1/3 = 5/6: cutSum at (5, 6) = "5/6 ≤ 5/6" = true. -/
example : cutSum (constCut 1 2) (constCut 1 3) 5 6 = true := by decide

end E213.Math.Real213.CutSumTest
