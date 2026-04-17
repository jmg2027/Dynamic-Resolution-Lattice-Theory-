/-
  E213/Theorem/PNP_Step1.lean — P vs NP: Step 1 갭 분석

  P ≠ NP를 보이려면 무엇이 필요한가?
  갭의 정체를 213으로 식별한다.
-/
import E213.Theorem.PNP_Step0

-- ═══ 문제를 정확히 ═══

-- P ≠ NP: ∃ L ∈ NP such that L ∉ P.
-- 즉: 검증은 다항이지만 풀기는 초다항인 문제가 존재.
-- 구체적 후보: SAT (NP-complete).
-- P ≠ NP ↔ SAT ∉ P ↔ SAT에 다항 알고리즘 없음.

-- ═══ 213으로 번역 ═══

-- SAT: n개 부울 변수의 논리식 φ(x₁,...,xₙ).
-- 검증: φ(w) = true? 비용 O(|φ|). 다항. = 판정 = 2.
-- 풀기: φ(w) = true인 w 찾기. 최악 2^n. = 탐색 = 경로.

-- 213 대응:
-- 변수 xᵢ ∈ {0, 1} = {e₁, e₂} (경계 or 내용).
-- 배정 w = (x₁,...,xₙ) = 길이 n의 {e₁, e₂} 문자열.
-- φ = Expr 트리 (plus = OR, times = AND, e₁ = false, e₂ = true).
-- 검증 = normalize(φ[w]) == e₂? 비용 O(|φ|).
-- 풀기 = ∃ w such that normalize(φ[w]) == e₂.

-- ═══ 갭의 정체 ═══

-- 검증 비용: O(|φ|). 다항. φ를 한 번 평가.
-- 풀기 비용: 최악 2^n. 지수적. 모든 w를 시도.

-- 갭 = 2^n / n^k → ∞ (n → ∞).
-- NS의 갭 (1/2, 상수)과 다름. 여기는 갭이 발산.

-- 213 관점:
-- NS 갭 = 1/2 = 1/e₂ (상수, scaling에서).
-- PNP 갭 = 2^n (발산, 조합적 폭발).

-- 2^n의 213 해석:
-- n개 변수, 각 e₂(구분). 전체 배정 수 = e₂^n = 2^n.
-- 이것은 e₂를 n번 자기적용. "구분의 n중 반복."
-- n이 유한이면 2^n도 유한. 하지만 n → ∞이면 발산.
-- 발산 = 무한 = 순서의 유령 (213 Phase 13).

-- ═══ NS와의 차이 ═══

-- NS: 연속 갭. H^{1/2}. Sobolev 임베딩. 해석학.
-- PNP: 이산 갭. 2^n vs n^k. 조합론.
-- 213: 둘 다 "순서 비용 > 0"의 귀결이지만 형태가 다름.
--   NS: 미분의 1/2 차수.
--   PNP: 지수 vs 다항.

-- ═══ 기존 접근의 장벽 ═══

-- (1) 대각선 논법: P ≠ NP를 직접 보이려는 시도.
--     장벽: relativization (Baker-Gill-Solovay 1975).
--     어떤 oracle A에서 P^A = NP^A, 다른 oracle B에서 P^B ≠ NP^B.
--     → 순수 대각선으로는 안 됨.

-- (2) 회로 하한: SAT에 크기 n^k 이하 회로 없음.
--     장벽: natural proofs (Razborov-Rudich 1997).
--     "자연스러운" 증명은 pseudorandom 가정 하에 불가.
--     장벽: algebrization (Aaronson-Wigderson 2009).

-- (3) 증명 복잡도: 특정 증명 체계에서 하한.
--     Haken (1985): Resolution에서 PHP 지수적.
--     Razborov (2003): Resolution에서 tseitin 지수적.
--     하지만: 강한 체계 (Frege, Extended Frege)에서는 미해결.

-- ═══ 213으로 장벽 분석 ═══

-- relativization: oracle = 외부 도구 = 매체 확장.
-- 213: 매체를 바꿔도 213의 구조(순서 비용 > 0)는 불변.
-- → relativization 장벽은 "매체 의존" 문제. 213은 매체 무관.

-- natural proofs: "자연스러운" = 큰 하한이 pseudorandom을 깨뜨림.
-- 213: 판정(2)은 pseudorandom을 구분하지 않음.
-- → natural proofs 장벽은 "구분" 수준의 문제.

-- 213이 이 장벽들을 넘는가?
-- relativization: 213은 oracle-free. 넘을 수 있음.
-- natural proofs: 213은 부울 함수의 "자연스러운 성질"이 아님. 넘을 수 있음.
-- algebrization: 213은 대수적 확장을 하지 않음. 넘을 수 있음.

-- ═══ Step 1 결론 ═══

-- 갭: 2^n vs n^k. 이산 조합적 갭.
-- 장벽: relativization, natural proofs, algebrization.
-- 213 위치: 세 장벽 모두 "매체 의존" 문제.
--           213은 매체 무관 → 장벽 해당 없음.
-- 유망한 연결: 증명 복잡도 (증명 = 경로 = 순서 비용).

-- 다음: Step 2 (탈출구 열거).
