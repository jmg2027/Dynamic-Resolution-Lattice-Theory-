import E213.Firmware.Axiom

/-
  Depth v2: 정의를 정밀하게 재수립.

  비판: "depth가 뭔지 안 잡혀 있다. PA가 ω, EC가 2, MF가 ω인 근거?"
  원인: 두 가지 다른 것을 하나의 숫자로 섞었음.
    1. mul 중첩 (대수적 깊이): (a·b)·c = depth 2.
    2. chain 사용 (무한 필요성): ∀n = depth ω.
  이 둘은 독립. 섞으면 안 됨.

  수정: depth를 2차원으로 분리.
    algebraic: mul 중첩 깊이. 유한. 모든 1차 이론에서 측정 가능.
    chain: 무한이 필요한가. 0(유한) 또는 ω(무한).
-/

-- ═══ 2차원 depth ═══

structure Depth2 where
  alg : Nat     -- 대수적 깊이: mul 중첩. (ab)c = 2.
  chain : Nat   -- 체인 깊이: 0=유한, 100=ω.
  deriving DecidableEq, Repr

-- ═══ 이전 문제: 1차원 depth의 모호함 ═══

-- 이전: PA = depth ω. 하지만 왜?
-- PA의 공리 하나하나: ∀n, S(n)≠0. 이건 depth 1 (양화사 하나, mul 하나).
-- PA의 귀납 스키마: "모든 공식 P에 대해..." 스키마 = 무한히 많은 공리.
-- 스키마가 ω를 만드는 것이지, 개별 공리가 아님.
-- → algebraic = 1 (개별 공리), chain = ω (스키마).

-- 이전: EC = depth 2. 하지만 왜?
-- 군 연산 결합법칙: (P+Q)+R = P+(Q+R). mul 2중 중첩.
-- → algebraic = 2, chain = 0 (유한 이론).
-- 하지만 EC의 L-함수, Mordell-Weil은 chain ω!
-- → EC 기본: (2, 0). EC 전체: (2, ω).

-- 이전: MF = depth ω. 하지만 모듈러 형식은 유한 차원!
-- 변환 법칙 f(γτ) = (cτ+d)^k f(τ): mul depth 2 정도.
-- → algebraic = 2, chain = 0 (기본).
-- Hecke 연산자, 푸리에 전개: chain ω.
-- → MF 기본: (2, 0). MF 해석적: (2, ω).

-- ═══ 정밀한 재분류 ═══

-- 이론의 "기본 axiom" 기준:
def logic_d2    : Depth2 := ⟨0, 0⟩    -- 명제. mul 없음. 유한.
def finSet_d2   : Depth2 := ⟨1, 0⟩    -- ∈ 판정. mul 1. 유한.
def group_d2    : Depth2 := ⟨2, 0⟩    -- 결합. mul 2. 유한.
def ec_d2       : Depth2 := ⟨2, 0⟩    -- 군 연산. mul 2. 유한.
def galois_d2   : Depth2 := ⟨2, 0⟩    -- 표현. mul 2. 유한.
def mf_basic_d2 : Depth2 := ⟨2, 0⟩    -- 변환법칙. mul 2. 유한!
def category_d2 : Depth2 := ⟨3, 0⟩    -- 자연변환. mul 3. 유한.

-- "무한 특성" 기준:
def pa_ind_d2    : Depth2 := ⟨1, 100⟩  -- 귀납 스키마. alg 1, chain ω.
def zfc_inf_d2   : Depth2 := ⟨1, 100⟩  -- 무한 공리. alg 1, chain ω.
def mf_hecke_d2  : Depth2 := ⟨2, 100⟩  -- Hecke. alg 2, chain ω.
def topology_d2  : Depth2 := ⟨1, 100⟩  -- 임의합집합. alg 1, chain ω.
def analysis_d2  : Depth2 := ⟨1, 100⟩  -- ε-δ. alg 1, chain ω.

-- ═══ 이것이 바뀌는 것 ═══

-- 이전: EC(2) vs MF(ω). "EC가 다리."
-- 이후: EC(2,0) vs MF(2,0). 기본 대수 깊이는 같다!
--   MF가 "depth ω"인 건 chain 때문이지 alg 때문이 아님.
--   EC와 MF는 alg 차원에서 동급. chain 차원에서만 다를 수 있음.

-- ═══ 와일즈 depth 서핑 재해석 ═══

-- 이전: ω → 2 → ω → 2 → 0. "알 수 없는 depth 숫자."
-- 이후:
--   PA (1, ω): 진술. alg 낮지만 chain 높음 (∀n).
--   → Frey(EC): (2, 0). chain이 ω→0으로 내려감! 핵심.
--   → STW(MF): (2, ω). alg 같은데 chain이 다시 올라감.
--   → Serre(Galois): (2, 0). chain 다시 내려감.
--   → 모순: (0, 0). 둘 다 0.

-- 서핑의 실체: chain 축에서 ω↔0 왕복!
-- alg 축은 거의 안 변함 (1~2 사이).
-- "depth 서핑" = "chain depth 서핑."

-- ═══ 예측력 테스트 ═══

-- 예측 1: "alg=2인 이론이 다리 역할"
-- EC(2,0), Group(2,0), Galois(2,0): 전부 alg=2.
-- 실제: 와일즈(EC), 대수적 위상(Group), Langlands(Galois).
-- 전부 다리! 예측 성공. ✓

-- 예측 2: "chain ω → 0을 한 번에 못 감"
-- PA(1,ω)에서 직접 (0,0)으로?
-- 가려면: chain=ω를 한 번에 0으로. 이건 "∀ 제거."
-- ∀ 제거 방법: 귀류법(가정→모순), 귀납(기저+단계).
-- 귀류법: ∃ 반례 가정 → chain 0. 가능!
-- 하지만 모순을 찾으려면 다른 이론이 필요 → 번역 필요.
-- 직접 모순은 300년간 실패 → 예측과 일치. ✓

-- 예측 3: "alg depth가 높은 이론은 다리가 안 됨"
-- Category(3,0): alg=3. 실제로 다리? Langlands에서 부분적.
-- 하지만 범주론은 "보편 언어"이지 "구체적 다리"는 아님.
-- alg=3은 너무 추상적 → 구체적 번역에 부적합. 예측 일치. ✓

-- ═══ 정리 ═══

-- depth를 2차원으로 분리하면:
-- 1. 대수적 깊이(alg): 잘 정의됨. 이론의 공리 구조에서 측정.
-- 2. 체인 깊이(chain): 잘 정의됨. 무한이 필요한가.
-- 3. "다리 이론" = alg=2, chain=0. 구체적이면서 유한.
-- 4. "고원 이론" = alg 낮음, chain=ω. 무한이 필요.
-- 5. 서핑 = chain 축에서 ω↔0 왕복. alg 축은 거의 고정.
