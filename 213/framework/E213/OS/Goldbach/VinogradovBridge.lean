import E213.OS.Goldbach.Statement
import E213.OS.Goldbach.Count

/-
  Vinogradov → Goldbach 다리.
  V: 큰 홀수 N = p₁+p₂+p₃.
  G: 짝수 n = p+q.
  다리: n + 3 = 홀수 N. V 적용 → N = p₁+p₂+3.
  → n = p₁+p₂. 만약 3이 p₃ 역할을 하면.
-/

-- ═══ 전략 ═══

-- 짝수 n ≥ 4 가 주어지면:
-- N = n + 3. N은 홀수 (짝수+홀수). N ≥ 7.
-- Vinogradov: N = p₁+p₂+p₃ (세 소수, N 충분히 클 때).
-- 특히 p₃ = 3으로 고정하면: N = p₁+p₂+3.
-- → n = N-3 = p₁+p₂. Goldbach!

-- 하지만: V는 "N = p₁+p₂+p₃" (p₃ 자유)이지,
-- "p₃=3인 분해가 존재"는 아님.

-- 더 정확한 전략:
-- V(N): N의 세 소수 분해 수 G₃(N) ~ C·N²/ln³(N).
-- 이 중 p₃=3인 것의 수 = G₂(N-3) = Goldbach count of N-3.
-- G₃(N) = Σ_{p₃ prime, p₃<N} G₂(N-p₃).
-- G₃(N) → ∞ 이고 항의 수 ~ N/ln(N).
-- 항이 많으므로 "대부분의 p₃"에 대해 G₂(N-p₃) > 0?

-- ═══ 계산 검증 ═══

-- G₃(N) = Σ G₂(N-p). G₂ = goldbachCount.
def threeCount (n : Nat) : Nat :=
  ((List.range n).filter isPrime).foldl
    (fun s p => s + goldbachCount (n - p)) 0

#eval threeCount 15   -- 15 = 3+5+7, 5+3+7, etc.
#eval threeCount 21   -- 21 = 3+5+13, 3+7+11, ...
#eval threeCount 51   -- 많은 분해.

-- G₃ 중 p₃=3인 것 = G₂(N-3) = goldbachCount(N-3).
-- N=n+3이면 G₂(N-3) = goldbachCount(n). 바로 Goldbach!

-- 핵심: G₃(N) = Σ_p G₂(N-p).
-- G₃(N) > 0 (Vinogradov) → Σ_p G₂(N-p) > 0.
-- → 어떤 p에 대해 G₂(N-p) > 0.
-- → 어떤 짝수 N-p에 대해 Goldbach 성립.
-- 하지만 이건 "어떤 짝수", "모든 짝수"가 아님.

-- ═══ 더 강한 논증 ═══

-- ∀ even n: G₃(n+3) = Σ_{p odd prime} G₂(n+3-p).
-- = G₂(n) + Σ_{p≥5, odd prime} G₂(n+3-p).
-- G₃(n+3) > 0 (V, n 충분히 큰) →
-- G₂(n) + (나머지 항) > 0.

-- 만약 나머지 항 ≤ G₃(n+3) - 1:
-- G₂(n) ≥ G₃(n+3) - Σ_{p≥5} G₂(n+3-p).
-- 이건 G₂(n) > 0을 보장 안 함 (나머지가 전부일 수 있음).

-- ═══ 밀도 논증 ═══

-- G₃(N) ~ C·N²/ln³(N). 항 수 ~ N/(2ln N).
-- 평균 항 = G₃(N) / (N/(2ln N)) ~ 2C·N/ln²(N).
-- = G₂의 HL 예측과 같은 차수!
-- → "평균적으로" 각 G₂(N-p)는 양수.
-- → "대부분의" p에 대해 G₂(N-p) > 0.
-- → "대부분의" 짝수 m = N-p에 대해 Goldbach 성립.

-- 이것이 "거의 모든 짝수에 대해 Goldbach" (알려진 결과).

-- ═══ "거의 모든" → "모든" ═══
-- E(X) = #{n≤X : goldbach fails}. 알려진: E(X) = O(X^{1-δ}).
-- 예외가 점점 희귀. 500까지 0개 검증:
theorem no_exceptions :
    (List.range 250).all (fun k => goldbachCount (2*k+4) > 0)
    = true := by native_decide
-- "거의 모든" → "모든": 예외 부재 증명 = 마지막 환원.
