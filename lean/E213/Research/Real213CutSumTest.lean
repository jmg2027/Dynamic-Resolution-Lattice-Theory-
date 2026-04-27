import E213.Research.Real213CutSum

/-!
# Research.Real213CutSumTest: cutSum 의 concrete verification on rationals

`Real213CutSum.lean` 의 cutSum 이 *constant cut* (rational reals) 위
에 서 의 정확 성 verification.

각 const cut 은 `fun m k => decide(a*k ≤ b*m)` 형식 — ratio a/b 의
Dedekind cut.  Sum a/b + a'/b' = (a*b' + a'*b)/(b*b').

## Verified cases

- 1 + 1 = 2 (constCut(1,1) ⊕ constCut(1,1) at 다 양 한 (m, k))
- 1/2 + 1/2 = 1
- 1/2 + 1/3 = 5/6
-/

namespace E213.Research.Real213CutSum

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

end E213.Research.Real213CutSum
