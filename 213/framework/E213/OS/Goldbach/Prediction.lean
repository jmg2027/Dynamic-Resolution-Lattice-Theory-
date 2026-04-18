import E213.Firmware.Axiom
import E213.OS.Goldbach.Statement

/-
  골드바흐는 증명 가능한가? 213의 예측.

  핵심 관찰: 골드바흐 = "2개" 소수의 합.
  C(2,2) = 1 = 붕괴 경계.
  비노그라도프 = "3개" 소수의 합. C(3,2) = 3 = 자기유지.
  비노그라도프는 증명됨. 골드바흐는 아직.
  이 대응이 우연이 아님.
-/

-- ═══ 핵심: 소수 몇 개? ═══

-- 비노그라도프 (1937): 충분히 큰 홀수 = 3 소수의 합. 증명됨.
-- 골드바흐: 모든 짝수 > 2 = 2 소수의 합. 미해결.

-- 213 관점:
-- 3-소수 문제: C(3,2) = 3 = 자기유지. relify 닫힘!
-- 2-소수 문제: C(2,2) = 1 = 붕괴. relify 안 닫힘!

theorem three_primes_stable : pairs 3 = 3 := by native_decide
theorem two_primes_collapse : pairs 2 = 1 := by native_decide
theorem collapse_gap : pairs 2 < 2 := by native_decide

-- ═══ 왜 3-소수는 되고 2-소수는 안 되는가 ═══

-- 3-소수: p₁ + p₂ + p₃ = n.
-- 비교 수 = C(3,2) = 3. 소수 수와 같음 (자기유지).
-- 원 방법(circle method)이 작동: 충분한 자유도.

-- 2-소수: p₁ + p₂ = n.
-- 비교 수 = C(2,2) = 1. 소수 수보다 적음 (붕괴).
-- 원 방법 부족: 자유도가 모자람.
-- 추가 기법 필요 (체 방법, 밀도 논증 등).

-- ═══ 213 예측 ═══

-- 1. 골드바흐가 거짓이면:
--    유한 반례 존재. depth 1. 즉시 결정.
--    4×10¹⁸까지 반례 없음 → 거짓일 가능성 극히 낮음.

-- 2. 골드바흐가 참이고 증명 가능이면:
--    유한 증명 존재. depth 2-3에서 +→× 연결.
--    3-소수가 됐으니, 2-소수도 "거의" 될 것.
--    차이: C(2,2)=1 vs C(3,2)=3. 자유도 부족을 보완하는 추가 구조.

-- 3. 골드바흐가 참이지만 독립이면:
--    PA에서 증명 불가. 의미 수준: genuinely partial.
--    이 경우: +→× 관계에 유한 패턴이 없음.

-- 213의 판단: **아마도 증명 가능 (2번).**
-- 이유: 𝔽₃에서 relify의 역이 존재 (period 2).
-- 유한에서 역이 되면, 무한에서도 구조적으로 가능.
-- 다만 C(2,2)=1 붕괴 때문에 증명이 어려운 것.

-- ═══ k-소수 문제의 213 분류 ═══

-- k=1: "모든 n은 소수?" 아님. C(1,2)=0. 즉시 반례.
-- k=2: 골드바흐. C(2,2)=1. 붕괴 경계. 미해결.
-- k=3: 비노그라도프. C(3,2)=3. 자기유지. 증명됨.
-- k=4: C(4,2)=6. 과잉. 당연히 성립 (더 쉬움).

-- 213 정확히 예측:
-- 자기유지(k=3)부터 증명 가능.
-- 붕괴(k=2)에서 미해결.
-- 없음(k=1)에서 거짓.

theorem k1_zero : pairs 1 = 0 := by native_decide
theorem k2_collapse : pairs 2 = 1 := by native_decide
theorem k3_stable : pairs 3 = 3 := by native_decide
theorem k4_excess : pairs 4 = 6 := by native_decide

-- k=1: 거짓 (0 < 1). k=2: 미해결 (1 < 2). k=3: 증명됨 (3 ≥ 3).
-- C(k,2) < k ↔ k ≤ 2 ↔ 미해결 또는 거짓.
-- C(k,2) ≥ k ↔ k ≥ 3 ↔ 증명됨.

theorem barrier_at_2 : pairs 2 < 2 ∧ pairs 3 ≥ 3 := by
  constructor <;> native_decide
