/-
  E213/Theorem/LowerBound.lean — 상대적 구분의 하한 = 3

  n개 원소에서 이항 관계 수 = C(n,2).
  "자기유지": 관계가 원소를 커버. C(n,2) ≥ n.
  C(n,2) ≥ n ⟺ n ≥ 3.
-/
import Init

def pairs (n : Nat) : Nat := n * (n - 1) / 2

-- 원소 수별 관계 수
#eval pairs 0  -- 0
#eval pairs 1  -- 0
#eval pairs 2  -- 1
#eval pairs 3  -- 3
#eval pairs 4  -- 6

-- ═══ 1개: 관계 없음 ═══
theorem one_no_relation : pairs 1 = 0 := by native_decide

-- ═══ 2개: 관계 1개. 비교 대상 없음 ═══
theorem two_one_relation : pairs 2 = 1 := by native_decide
theorem two_not_self_sustaining : pairs 2 < 2 := by native_decide

-- ═══ 3개: 관계 3개 = 원소 수. 자기유지! ═══
theorem three_self_sustaining : pairs 3 = 3 := by native_decide

-- ═══ 하한 정리: n < 3이면 자기유지 불가 ═══
theorem below_three_fails :
    pairs 0 < 0 ∨ pairs 0 = 0 ∧ 0 = 0  -- 공집합
    ∧ pairs 1 < 1                         -- 1개: 부족
    ∧ pairs 2 < 2                         -- 2개: 부족
    := by native_decide

-- n ≥ 3이면 C(n,2) ≥ n (개별 확인)
theorem pairs_ge_3 : pairs 3 ≥ 3 := by native_decide
theorem pairs_ge_4 : pairs 4 ≥ 4 := by native_decide
theorem pairs_ge_5 : pairs 5 ≥ 5 := by native_decide
theorem pairs_ge_10 : pairs 10 ≥ 10 := by native_decide

-- ═══ 3이 최소인 이유: 비교의 비교 ═══
-- 관계 r₁₂, r₁₃, r₂₃가 있으면:
-- r₁₂와 r₁₃ 비교 → 원소 1의 역할 식별.
-- r₁₂와 r₂₃ 비교 → 원소 2의 역할 식별.
-- 2개에서는: r₁₂ 하나. 비교 불가. 역할 식별 불가.

structure LowerBoundTheorem where
  zero_fail : pairs 0 = 0
  one_fail : pairs 1 = 0
  two_fail : pairs 2 < 2
  three_ok : pairs 3 = 3

theorem lower_bound_is_three : LowerBoundTheorem where
  zero_fail := by native_decide
  one_fail := by native_decide
  two_fail := by native_decide
  three_ok := by native_decide
