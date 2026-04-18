import E213.Goldbach.Statement

/-
  골드바흐 유한 검증.
  개별 n: depth 1. native_decide.
  범위 검증: depth 1 × bound. 여전히 유한.
-/

-- ═══ 개별 검증 ═══

theorem g4  : goldbach 4  = true := by native_decide
theorem g6  : goldbach 6  = true := by native_decide
theorem g8  : goldbach 8  = true := by native_decide
theorem g10 : goldbach 10 = true := by native_decide
theorem g28 : goldbach 28 = true := by native_decide

-- ═══ 범위 검증 ═══

-- 100까지 모든 짝수.
theorem verified_100 : goldbachUpTo 100 = true := by native_decide

-- 200까지.
theorem verified_200 : goldbachUpTo 200 = true := by native_decide

-- 500까지.
theorem verified_500 : goldbachUpTo 500 = true := by native_decide

-- ═══ 213 관점 ═══

-- 각 검증 = depth 1. mul 유한번. 완전한 의미.
-- verified_500 = 500개 × 가 전부 true.
-- 하지만: 501번째, 1000번째, ... 는 별도 검증 필요.
-- ∀n = 무한히 많은 검증 = depth ω.

-- 213의 유한 = 이 하는 일:
-- "500까지는 맞다." ← 의미 있음 (full).
-- "모든 n에 대해." ← 의미 전이 (partial).

-- ═══ 분해쌍 패턴 ═══

#eval (List.range 50).filterMap fun n =>
  if isEven n && n > 2 then goldbachPair n else none
-- [(2,2), (3,3), (3,5), (3,7), (5,7), (3,11), ...]
-- 작은 소수(3, 5, 7)가 자주 등장. 왜?
-- 작은 소수 = depth 0-1에서 이미 결정. "싸게" 구분 가능.
-- 큰 소수 = depth 높음. "비싸게" 구분.
-- 골드바흐는 "싼 소수"를 선호.
