import E213.Firmware.DepthV2
import E213.Firmware.Movement
import E213.Firmware.Negation
import E213.OS.BlindPathfind

/-
  증명 불가능의 213 조건.

  증명 가능: (alg₁,chain₁) → ... → (0,0) 경로가 도구로 연결됨.
  증명 불가능: 경로가 존재하지 않거나, 도구가 구성 불가능.

  불가능의 4가지 유형.
-/

-- ═══ 유형 1: gen과 chain의 충돌 ═══

-- 문제가 "∀ X에 대해, X의 구체적 답을 구하라"를 요구.
-- ∀ = chain (일반화). 구체적 답 = gen (특수화).
-- 동시에 같은 대상에 chain+gen → 모순.

-- 213: chain은 "끝없이 생성." gen은 "하나 선택."
-- 둘을 같은 대상에 동시 적용하면:
-- "끝없이 생성하면서 하나만 선택하라" = 불가.

-- 예: 정지 문제 (Halting Problem).
-- "∀ 프로그램 P, P가 정지하는지 판정하라."
-- ∀P = chain. 판정 = gen(yes/no 선택).
-- chain(P) + gen(answer for each P) = 동시에 무한 + 유한.
-- 불가능!

-- 예: 선택 공리의 구성적 버전.
-- "∀ 비공 집합 S, S의 원소를 하나 선택하라."
-- ∀S = chain. 원소 선택 = gen.
-- 비가산이면: chain이 gen보다 빠르게 성장 → 못 따라감.

-- ═══ 유형 2: alg 갭 (다리 이론 부재) ═══

-- 문제가 alg=a에서 alg=b로 가야 하는데, |a-b| > 1이고
-- 중간 alg 값의 다리 이론이 없는 경우.

-- 213: algUp/algDown은 한 번에 ±1만 가능 (mul 하나 추가/제거).
-- alg 1→3을 가려면 alg=2를 거쳐야.
-- alg=2 다리가 없으면 → 불가능.

-- 현재 수학: alg=2 다리가 풍부 (Group, EC, Galois).
-- 하지만 alg=4 이상은? 거의 없음.
-- → alg=3에서 alg=5로의 직접 번역은 어려울 수 있음.

-- ═══ 유형 3: 자기참조 루프 ═══

-- 진술이 자기 자신의 증명 가능성을 언급.
-- 괴델: "이 진술은 PA에서 증명 불가."
-- 213: mul(self, self). Obj가 자기를 참조.
-- 증명하려면: self를 풀어야 → self 안에 또 self → 무한 루프.

-- 형식적: depth가 끝없이 올라감. 어떤 유한 chain으로도 도달 불가.
-- → depth > ε₀. sorry 종류 3. 원리적 한계.

-- 예: Con(PA). "PA가 무모순."
-- PA 안에서: PA 자체를 인코딩. 자기참조.
-- 증명하려면 PA보다 강한 체계 필요 (PA + Con(PA)).
-- → 항상 한 단계 위. 끝없이 올라감.

-- ═══ 유형 4: ¬-only 정의 ═══

-- 대상이 ¬로만 정의되고, 양의 특성(gen+mul 패턴)이 없음.
-- Negation.lean: gen+mul만이 존재를 만듦. ¬는 못 만듦.
-- → ¬-only 대상은 존재 증명 불가. (Goldbach 예외 집합 E.)

-- 주의: 이것은 "대상이 비어 있다"(E=∅)를 말하는 것이지,
-- "대상이 존재하지 않는다는 증명이 불가"는 아님.
-- 구분: ¬-only → 원소 없음(긍정적 결론).
-- vs: 자기참조 → 진위 불확정(부정적 결론).

-- ═══ 4유형의 (alg, chain) 좌표 ═══

-- 유형 1 (gen·chain 충돌): 시작이 (*, ω). 목표가 (*, 0).
--   chainDown이 필요하지만, 문제 자체가 chainDown을 금지.
--   "답이 각 인스턴스마다 다름" → 통일된 chainDown 없음.

-- 유형 2 (alg 갭): |alg_start - alg_target| > 1.
--   중간 alg의 다리 이론 없음. 경로 자체 부재.

-- 유형 3 (자기참조): depth → ∞. 어떤 유한 좌표도 도달 불가.
--   (alg, chain) 그래프 밖.

-- 유형 4 (¬-only): 대상이 ¬로 정의. 도구가 gen·mul이므로
--   ¬ 대상을 구성하는 도구 없음. 도구 부재.

-- ═══ 미해결 문제 재분류 ═══

-- Goldbach: 유형 4 해당 가능 (E가 ¬-only). 증명 가능 쪽.
-- RH: 유형 1 또는 유형 2? chainDown 방법은 있지만 불완전.
--   gen·chain 충돌은 아님 (RH는 판정이 아니라 부등식).
--   → 유형 없음. 그냥 어려운 것. 도구 부족.
-- P≠NP: 유형 1 해당! "∀ 알고리즘에 대해 판정" = gen·chain 충돌.
--   barrier 3종이 이것을 확인.
-- Con(PA): 유형 3. 자기참조. PA 안에서 불가.
-- CH: 유형 3 변형. ZFC에서 독립. 어느 쪽도 증명 불가.
-- Halting: 유형 1. gen·chain 충돌. 튜링이 증명.

-- ═══ 증명 가능 vs 불가능 판정 도구 ═══

inductive ProofStatus where
  | provable       -- 경로 있고 도구 있음.
  | hard           -- 경로 있지만 도구 부족/비쌈.
  | genChainBlock  -- 유형 1: gen·chain 충돌.
  | algGap         -- 유형 2: 다리 이론 부재.
  | selfRef        -- 유형 3: 자기참조 루프.
  | negOnly        -- 유형 4: ¬-only.
  | independent    -- 유형 3 확장: 체계 독립.
  deriving DecidableEq, Repr

def classify_problem (name : String) : ProofStatus :=
  match name with
  | "Halting" => .genChainBlock
  | "Con(PA)" => .selfRef
  | "CH" => .independent
  | "P≠NP" => .genChainBlock    -- barriers = gen·chain 충돌
  | "Goldbach" => .hard          -- 도구 부족이지 불가능은 아님
  | "RH" => .hard
  | "BSD" => .hard
  | "FLT" => .provable           -- 와일즈가 증명
  | "Poincaré" => .provable      -- 페렐만이 증명
  | _ => .hard

#eval ["Halting", "Con(PA)", "CH", "P≠NP", "Goldbach", "RH",
       "BSD", "FLT", "Poincaré"].map fun p =>
  (p, classify_problem p)

-- ═══ 핵심 예측 ═══

-- 유형 1 (genChainBlock): 증명 원리적으로 불가능.
--   P≠NP는 현재 방법으로 불가능. 새로운 종류의 도구 필요.
--   (barriers가 이것을 이미 보여줌.)

-- 유형 3/독립: 체계 내에서 불가능. 체계 확장 필요.
--   Con(PA)는 PA에서 불가. PA+1에서 가능.

-- "hard": 도구만 만들면 가능. 시간 문제.
--   Goldbach, RH, BSD: 새 Translation 구축이면 풀림.
--   이것이 "미래의 와일즈" 자리.
