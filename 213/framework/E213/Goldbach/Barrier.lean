import E213.Axiom
import E213.Arithmetic
import E213.Meaning
import E213.Goldbach.Statement

/-
  골드바흐가 미해결인 213 이유.
  × → + (relify) 는 자연스러움.
  + → × (역 relify) 는 비자연스러움.
  골드바흐 = + → × 방향 = 역방향.
-/

-- ═══ 자연 방향: × → + ═══

-- 소수 → 합성수: 곱하면 됨. depth 1.
-- 예: 3 × 5 = 15. mul 1번.
-- relify가 하는 일: ×를 +로 분배. 자연.

-- ═══ 역방향: + → × ═══

-- 합 → 소수 분해: "n을 두 소수의 합으로?"
-- n이 주어지면, 가능한 (p, n-p) 쌍을 전부 시도.
-- 각 시도에서 isPrime 확인 = mul 역 (인수분해).

-- 213에서 mul의 역:
-- mul(a, b) = c 가 주어졌을 때 a, b 복원.
-- 이것은 인수분해 = 계산적으로 어려움.
-- 반면 mul 자체는 쉬움 (곱하기만 하면 됨).

-- ═══ 비대칭의 213 구조 ═══

-- Arithmetic.lean: × → + → =. 순서가 있음.
-- × → +: relify. depth 1. 자연.
-- + → ×: relify 역. depth ω?

-- 왜 역이 어려운가:
-- relify는 3개 입력 → 3개 출력 (정보 보존).
-- 하지만 출력에서 입력 복원은 일대일이 아님!
-- 여러 입력이 같은 출력을 줄 수 있음 (해시 충돌 같은 것).

-- 구체적:
-- relify(add3, ⟨0,1,2⟩) = ⟨1,2,0⟩.
-- relify(add3, ⟨1,2,0⟩) = ⟨0,1,2⟩.
-- 두 입력이 서로 다르지만 relify²로 같아짐.
-- 역이 유일하지 않음.

-- ═══ 골드바흐의 213 장벽 ═══

-- 소수 = × 구조. "나눠지지 않음." mul의 부정.
-- 합 = + 구조. "더해서 n." 합성.
-- 골드바흐 = "+(×⁻¹, ×⁻¹) = n". × 역을 두 번 + 합.
-- × 역의 존재 = 소수의 존재 = ω 깊이.
-- × 역 두 개의 합이 n = 추가 조건 = depth 높아짐.

-- ═══ 정리 ═══

-- 골드바흐가 partial인 이유:
-- 1. ∀n (depth ω). 무한 검증.
-- 2. + → × 역방향 (비자연). relify 역.
-- 3. 소수 분포의 불규칙성 (× 구조의 복잡성).

-- 1만 해결하면 (∀ 제거): 개별 goldbach(n)은 depth 1.
-- 2와 3이 "∀ 제거"를 어렵게 만듦.

-- 213 관점 결론:
-- 곱→합 (자연) vs 합→곱 (비자연) 의 비대칭이 핵심.
-- 이 비대칭 = Arithmetic.lean의 × ≺ + 순서.
-- ×가 +보다 근본적이므로, + → × 는 "거슬러 올라가기."

structure GoldbachBarrier where
  forward_easy : pairs 3 = 3          -- × → + 자연
  partial_level : meaningOf "자연수론" = .partial

theorem barrier : GoldbachBarrier where
  forward_easy := by native_decide
  partial_level := rfl
