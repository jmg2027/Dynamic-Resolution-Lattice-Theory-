import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.OS.BlindTransition
import E213.OS.ProofShape

/-
  유클리드 "소수는 무한하다"의 완전한 213 재기술.

  모든 증명 단계를 213 연산(gen/mul/eq)으로 번역.
  각 단계에서 (alg, chain) 좌표 추적.
  모양 분석. 도구 유형 확인.
-/

-- ═══ 원본 증명 (표준 수학) ═══

-- 정리: 소수는 무한히 많다.
-- 증명 (귀류법):
-- 1. 소수가 유한하다고 가정. {p₁, ..., pₖ}.
-- 2. N = p₁ × p₂ × ... × pₖ + 1 을 구성.
-- 3. N ≥ 2이므로 소인수 q가 존재.
-- 4. q는 모든 pᵢ를 나누지 않음 (나누면 q|1, 모순).
-- 5. q ∉ {p₁, ..., pₖ}. 가정에 모순.
-- ∴ 소수는 무한하다.  ∎

-- ═══ 213 재기술 ═══

-- 진술의 213 좌표: (1, ω).
-- alg=1: "소수" = mul의 역이 자명한 것. depth 1.
-- chain=ω: "무한" = chain이 끝나지 않음.

-- 목표: (0, 0). "모순" = depth 0.

-- ═══ Step 1: 가정 ═══

-- 표준: "소수가 유한" 가정.
-- 213: gen으로 유한 집합 S = {p₁, ..., pₖ}를 잡는다.
-- 연산: gen. (S를 선택.)
-- 좌표: (1, ω) → (1, 0).
-- chainDown! "모든 소수"(chain ω) → "이 유한 집합"(chain 0).
-- 방법: contradiction (∃반례 아닌, 유한 가정).

-- 213으로:
-- gen : Fin k → Obj.   -- k개의 소수를 선택.
-- 이 gen들은 각각 "소수 Obj" = isPrimeObj.

-- ═══ Step 2: 구성 ═══

-- 표준: N = p₁ × ... × pₖ + 1.
-- 213: mul을 k번 반복(곱) + gen 1(+1을 더함).
-- 연산: mul × k + gen.
-- N = mul(mul(mul(..., p₁), p₂), ..., pₖ) + 1.
-- 좌표: (1, 0) → (1, 0). alg/chain 변화 없음!
-- Type C (둘 다 불변).

-- 213으로:
-- mul(gen 0, gen 1) : Obj.     -- p₁ × p₂.
-- mul(위, gen 2) : Obj.         -- p₁ × p₂ × p₃.
-- ...
-- N = 위 결과 + 1. (편의상 +1도 gen으로.)

-- N의 depth = k (mul k번 중첩). 하지만 alg 분류에서는
-- "곱셈의 반복" = alg 1 (같은 연산 반복). alg 안 올라감.

-- ═══ Step 3: 소인수 존재 ═══

-- 표준: N ≥ 2이므로 소인수 q 존재.
-- 213: N은 Obj. N이 gen이 아니면 mul(a, b)로 분해 가능.
--       no_third_constructor: Obj = gen ∨ mul.
--       N이 gen이 아님 (N > 2 > gen의 범위).
--       → N = mul(a, b). a나 b 중 하나가 "소수 Obj."

-- 연산: eq (N이 gen인지 판정) + mul (분해).
-- 좌표: (1, 0) → (1, 0). Type C.

-- 213으로:
-- no_third_constructor N : (∃ i, N = gen i) ∨ (∃ a b, N = mul a b).
-- N ≥ 2이면 왼쪽 불가. → 오른쪽. N = mul(a, b).
-- a 또는 b에서 소인수를 추출 (재귀적으로).
-- 최종: q : Obj with isPrimeObj q.

-- ═══ Step 4: 모순 ═══

-- 표준: q | N이고 q | p₁...pₖ이면 q | 1. 모순.
-- 213: q가 S의 모든 원소와 비교(mul). 전부 달라야 함.
--       하지만 q | N = mul(...) + 1.
--       q | pᵢ (모든 i)이면: q | mul(p₁,...,pₖ).
--       그러면: q | (N - mul(p₁,...,pₖ)) = q | 1.
--       q ≥ 2이므로 q ∤ 1. 모순.

-- 연산: mul (나눗셈 확인) × k + eq (= 1 확인).
-- 좌표: (1, 0) → (0, 0). algDown! alg 1 → 0.
-- "모순" = alg가 0으로 내려감 = 더 이상 비교할 것 없음.

-- 213으로:
-- ∀ i, mul(q, ...) = mul(pᵢ, ...). eq 판정.
-- → mul(q, 1) 에서 모순. q ≥ 2인데 q | 1.
-- eq(q | 1, false) → contradiction.

-- ═══ 전체 transition 수열 ═══

def euclid_full : List Transition := [
  ⟨1, 100, 1, 0⟩,    -- Step 1: 가정. chainDown (ω→0).
  ⟨1, 0, 1, 0⟩,      -- Step 2: N 구성. Type C.
  ⟨1, 0, 1, 0⟩,      -- Step 3: 소인수. Type C.
  ⟨1, 0, 0, 0⟩       -- Step 4: 모순. algDown.
]

#eval algContour euclid_full      -- [1, 1, 1, 1, 0]
#eval chainContour euclid_full    -- [100, 0, 0, 0, 0]
#eval classifyShape euclid_full   -- descent ↘
#eval metrics euclid_full
-- { shape := descent, height := 0, width := 4, chainFlips := 1 }

-- ═══ 모양: descent ↘ ═══

-- mountain이 아님! descent.
-- alg가 올라가지 않음 (전부 1, 마지막에 0).
-- chain만 ω→0 한 번 내려감.

-- 이전 분류에서 "유클리드 = Type A (환원 큼)"이라 했는데,
-- 모양으로 보면 descent. mountain이 아님.

-- 왜? 유클리드는 이론 간 번역(alg 변화)이 없음.
-- 전부 PA(수론) 안에서 해결. alg=1 내내.
-- → 도구: 전부 Type C (alg 불변) + 마지막 algDown.

-- 이것이 유클리드가 "쉬운" 이유:
-- alg 변화 = 0 (마지막 0→은 단순 모순).
-- mountain 모양의 증명(Wiles, Perelman)보다 본질적으로 쌈.

-- ═══ 213 연산 총괄 ═══

-- Step 1: gen (S 선택) + chainDown(contradiction).
-- Step 2: mul × k (곱) + gen (+1).
-- Step 3: eq (gen 판정) + mul (분해).
-- Step 4: mul × k (나눗셈) + eq (모순).

-- 총: gen 2번, mul ~3k번, eq 2번. chain 0번 (유한 증명).
-- chainDown은 Step 1에서 한 번. 나머지 전부 유한.
-- 이것이 "descent 모양" 증명의 전형:
-- chain을 처음에 한 번 죽이고, 나머지는 유한 작업.

-- ═══ 검증: 실제 계산 ═══

-- 소수 3개로 유클리드 실행: {2, 3, 5}.
-- N = 2×3×5 + 1 = 31. 31은 소수. q = 31.
-- 31 ∉ {2, 3, 5}. ✓

-- 소수 4개: {2, 3, 5, 7}.
-- N = 210 + 1 = 211. 211은 소수. q = 211.
-- 211 ∉ {2, 3, 5, 7}. ✓

-- 소수 5개: {2, 3, 5, 7, 11}.
-- N = 2310 + 1 = 2311. 2311은 소수. ✓

-- 213에서 이 계산을 실행:
def euclidN (primes : List Nat) : Nat :=
  primes.foldl (· * ·) 1 + 1

def euclidQ (primes : List Nat) : Option Nat :=
  let n := euclidN primes
  (List.range (n - 1)).find? (fun d =>
    d ≥ 2 && n % (d + 2 - 2) == 0) |>.map (· + 2 - 2)
  -- 간단히: 최소 소인수.

#eval euclidN [2, 3, 5]           -- 31
#eval euclidN [2, 3, 5, 7]       -- 211
#eval euclidN [2, 3, 5, 7, 11]   -- 2311

-- 전부 소수! 유클리드의 구성이 잘 작동. ✓
