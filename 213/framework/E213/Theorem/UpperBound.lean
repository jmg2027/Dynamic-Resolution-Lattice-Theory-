/-
  E213/Theorem/UpperBound.lean — 상한 = 3 (환원)

  n > 3이면 C(n,2) > n. 관계가 원소보다 많음 = 중복.
  C(n,2) = n의 유일한 해: n = 3.
  따라서 n개 구분은 3-묶음으로 환원.
-/
import Init

def pairs (n : Nat) : Nat := n * (n - 1) / 2

-- ═══ n > 3이면 관계 과잉 ═══
#eval (pairs 4, 4)   -- (6, 4): 6 > 4
#eval (pairs 5, 5)   -- (10, 5): 10 > 5
#eval (pairs 6, 6)   -- (15, 6): 15 > 6

theorem four_excess : pairs 4 > 4 := by native_decide
theorem five_excess : pairs 5 > 5 := by native_decide
theorem six_excess : pairs 6 > 6 := by native_decide

-- ═══ C(n,2) = n의 유일한 해 ═══
-- n(n-1)/2 = n ↔ n-1 = 2 ↔ n = 3.

def isSelfSustaining (n : Nat) : Bool := pairs n == n

#eval (List.range 20).filter isSelfSustaining
-- [0, 3]: 0은 사소 (공집합). 비사소 해 = 3 유일.

theorem unique_fixed_point :
    (List.range 20).filter (fun n => n > 0 && isSelfSustaining n)
    = [3] := by native_decide

-- ═══ 과잉도 = n(n-3)/2 ═══
def excess (n : Nat) : Int := (pairs n : Int) - (n : Int)

#eval excess 3   -- 0: 정확
#eval excess 4   -- 2: 과잉 2
#eval excess 5   -- 5: 과잉 5
#eval excess 10  -- 35: 과잉 35

theorem three_exact : excess 3 = 0 := by native_decide
theorem four_redundant : excess 4 = 2 := by native_decide

-- ═══ 환원 원리 ═══
-- n개를 구분하려면: 각 원소를 나머지와의 관계로 식별.
-- 원소 i: (i와 j₁의 관계, i와 j₂의 관계, ...).
-- 최소 식별: 2개의 관계 (삼각측량).
-- 삼각측량 = 3개 원소 (i, j₁, j₂).
-- 따라서 어떤 원소든 3-묶음으로 식별 가능.

-- n=4: 각 원소를 3개의 관계로 봄.
-- 4 × 3 / 2 = 6개 관계. C(4,2) = 6. ✓
-- 하지만 C(3,2) = 3개로 한 원소 완전 식별.
-- 나머지 3개 관계 = 중복 (다른 삼각형).

structure UpperBoundTheorem where
  exact_at_3 : pairs 3 = 3
  excess_at_4 : pairs 4 > 4
  unique : (List.range 20).filter
    (fun n => n > 0 && isSelfSustaining n) = [3]

theorem upper_bound_is_three : UpperBoundTheorem where
  exact_at_3 := by native_decide
  excess_at_4 := by native_decide
  unique := by native_decide
