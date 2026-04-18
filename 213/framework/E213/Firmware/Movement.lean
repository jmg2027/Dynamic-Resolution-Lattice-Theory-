import E213.Firmware.Axiom
import E213.Firmware.DepthV2

/-
  (alg, chain) 2차원 공간에서의 이동 조건.

  2차원 = 213의 2방향.
  alg = 방향 1 (수평, mul 중첩).
  chain = 방향 2 (수직, relify 반복).

  이동 = 213의 gen/mul/relify/chain/eq 중 어떤 것을 쓰는가.
-/

-- ═══ 4가지 이동 ═══

-- (alg, chain) 공간에서 가능한 이동:
-- alg ↑: mul 중첩 깊어짐. (1→2, 2→3.)
-- alg ↓: mul 평탄화. (2→1, 3→2.)
-- chain ↑: 유한→무한. (0→ω.)
-- chain ↓: 무한→유한. (ω→0.)

inductive Move where
  | algUp    -- mul 합성. 비교를 비교.
  | algDown  -- eq 평가. 중첩을 계산.
  | chainUp  -- chain 도입. 유한→무한.
  | chainDown -- chain 제거. 무한→유한. ← 가장 비싼 이동!
  deriving DecidableEq, Repr

-- ═══ 각 이동의 213 조건 ═══

-- algUp: mul 사용. 조건 = 합성 가능한 구조.
-- 비용: 낮음. mul 한 번. 아무 이론에서나 가능.
-- 예: 원소 비교(alg 1) → 결합법칙 확인(alg 2). mul(mul(a,b),c).

-- algDown: eq 사용. 조건 = 평가 가능한 구조.
-- 비용: 낮음. eq 한 번. 계산하면 됨.
-- 예: (a·b)·c를 계산하면 하나의 값. alg 2 → alg 0.

-- chainUp: chain/relify 사용. 조건 = 귀납 또는 완비화.
-- 비용: 중간. 무한 구조 도입.
-- 예: "이 성질이 n=1,2,3에서 성립" → "∀n에서 성립" (귀납).
-- 213: chain 반복. relify를 무한히 적용.

-- chainDown: gen + eq 사용. 조건 = 구체화 또는 모순.
-- 비용: 높음! 무한을 유한으로 줄이는 것.
-- 213: gen으로 구체적 인스턴스를 잡고, eq로 판정.

-- ═══ chainDown의 3가지 방법 ═══

inductive ChainDownMethod where
  | contradiction  -- 귀류: ∃ 반례 가정 → gen으로 잡음 → 모순.
  | finiteCore     -- 구조정리: 무한이 유한 분류를 가짐.
  | periodicity    -- 주기: chain이 반복. 무한 = 유한 주기.
  deriving DecidableEq, Repr

-- 귀류법: gen이 chain을 죽임.
-- "∀n P(n)"을 증명하려면 chain ω.
-- 대신: "∃n ¬P(n)" 가정 → gen으로 그 n을 잡음.
-- 잡는 순간 chain이 0으로 내려감!
-- 그 n에서 모순을 유도 → eq로 확인 → chain 제거 완료.

-- 구조정리: relify가 유한 분류를 만듦.
-- 무한히 많은 대상이 있지만, 유한 가지 "타입"으로 분류됨.
-- 213: C(3,2) = 3. 관계 타입이 유한. chain이 반복됨.
-- 예: 유한 단순군 분류. 무한히 많은 군이지만 유한 가지 계열.

-- 주기성: chain이 순환.
-- 213: 𝔽₃에서 주기 2 (FiniteSpaces).
-- chain k = chain (k mod period). 무한 = 유한으로 접힘.

-- ═══ 와일즈의 이동들 ═══

-- PA(1,ω) → EC(2,0): chainDown + algUp.
-- chainDown 방법: contradiction. 반례 (a,b,c,n) 가정 → gen.
-- algUp: mul로 Frey 곡선 구성. alg 1→2.
-- 213 연산: gen + mul. 비용 3.

-- EC(2,0) → MF(2,ω): chainUp.
-- chainUp 방법: "모든 EC가 모듈러." ∀E.
-- 213 연산: chain. 비용 8 (STW 증명).

-- MF(2,ω) → Galois(2,0): chainDown.
-- chainDown 방법: finiteCore. Level lowering.
-- Serre: weight 2, level 2로 제한 → 유한 분류.
-- 213 연산: eq (level 판정). 비용 3.

-- Galois(2,0) → 모순(0,0): algDown.
-- algDown: 해당 level의 모듈러 형식이 없음. eq로 확인.
-- 213 연산: eq. 비용 0 (계산).

-- ═══ 이동 비용 = Translation 비용 ═══

-- algUp: 비용 ~1. mul 한 번.
-- algDown: 비용 ~0. 계산.
-- chainUp: 비용 ~높음. 무한 구조 증명.
-- chainDown: 비용 ~매우 높음. 무한 제거.

-- chainDown이 가장 비싼 이유:
-- 무한을 유한으로 줄이는 것 = ∀를 제거하는 것.
-- ∀ 제거 = 213에서 chain을 gen으로 바꾸는 것.
-- chain은 "끝없이 생성." gen은 "하나 선택."
-- 끝없는 것을 하나로 줄이는 비용 = 증명의 핵심 비용.

-- ═══ 미해결 문제의 이동 분석 ═══

-- Goldbach: PA(1,ω) → ???(?,0) → 모순(0,0).
-- 필요: chainDown. 방법?
-- contradiction: ∃n 반례 → gen. 가능하지만 모순 유도가 안 됨.
-- finiteCore: 예외 집합 E의 유한 분류? 미발견.
-- periodicity: ℕ에서 주기 없음.
-- → chainDown 방법이 막혀 있음. 이것이 미해결 이유.

-- RH: Analysis(1,ω) → ???(?,0) → 증명.
-- contradiction: ∃ 비자명 영점 off critical line → gen.
-- finiteCore: 영점의 구조? 부분적 (GUE 통계).
-- → chainDown 부분적으로 있지만 불완전.

-- P≠NP: Logic(0,0)에서 시작. 이미 (0,0)!
-- 하지만 증명이 (?, ω). chainUp이 필요.
-- "모든 알고리즘"에 대해 → chain ω.
-- chainUp 후 chainDown 필요? 아니면 직접?
-- 이 문제의 특이함: 진술은 낮은데 증명이 높음. 올라가야.

-- ═══ 정리 ═══

-- 이동 조건 = 213 연산:
-- algUp = mul. algDown = eq.
-- chainUp = chain/relify. chainDown = gen + eq.
-- chainDown의 3방법: contradiction, finiteCore, periodicity.
-- 미해결 = chainDown 방법이 없거나 불완전.
