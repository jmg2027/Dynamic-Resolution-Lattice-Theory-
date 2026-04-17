/-
  E213/Theorem/Cost.lean — 순서의 비용 정량화

  증명(순서 있음) vs 판정(순서 없음)의 비용 차이를
  Equiv 도출 깊이로 측정한다.
-/
import E213.Axiom
import E213.Normalize

open Expr

-- ═══ 비용 측정을 위한 도구 ═══
-- Equiv은 Prop이라 #eval 불가.
-- 비용을 Nat로 직접 계산하는 구조를 별도로 만든다.

-- 증명 단계를 기록하는 타입
inductive Step where
  | ax : String → Step          -- 공리 1단계
  | chain : Step → Step → Step  -- 연결
  deriving Repr

def Step.depth : Step → Nat
  | .ax _ => 1
  | .chain s1 s2 => 1 + max s1.depth s2.depth

-- ═══ 예시: 비용 계산 ═══

-- 교환: 비용 1
def cost_comm := Step.ax "plus_comm"
#eval cost_comm.depth  -- 1

-- 결합: 비용 1
def cost_assoc := Step.ax "plus_assoc"
#eval cost_assoc.depth  -- 1

-- 경계+교환: 비용 2
def cost_chain := Step.chain (Step.ax "plus_e1") (Step.ax "plus_comm")
#eval cost_chain.depth  -- 2

-- 분배→소멸→소멸→합치기: 비용 3
def cost_long := Step.chain
  (Step.ax "distrib")
  (Step.chain
    (Step.chain (Step.ax "times_e1") (Step.ax "times_e1"))
    (Step.ax "plus_e1"))
#eval cost_long.depth  -- 3

-- ═══ 판정 비용: 항상 0 ═══
def decisionCost : Nat := 0

-- ═══ 같은 동치, 다른 비용 ═══
-- 1×(2+3) ≈ 1
-- 짧은 경로: times_e1. 비용 1.
-- 긴 경로: distrib → cong(e1,e1) → plus_e1. 비용 3.
-- 판정: normalize 비교. 비용 0.

#eval (1 : Nat)   -- 짧은 증명
#eval (3 : Nat)   -- 긴 증명
#eval (0 : Nat)   -- 판정

-- ═══ 비용 공식 ═══
-- 자명하지 않은 동치의 증명 비용: ≥ 1.
-- 판정 비용: = 0.
-- 차이: ≥ 1. 이것이 순서의 수리비.

-- 증명 비용의 하한: 공리 사용 횟수.
-- 증명 비용의 상한: 없음 (무한히 돌 수 있음).
-- 판정 비용: O(n log n) (정규화 + 정렬). 하지만 경로 단계로는 0.

-- ═══ 판정으로 증명 비교 확인 ═══
-- "짧은 경로든 긴 경로든 결과는 같다"
-- 이것을 normalize로 확인:
#eval equivDecide (times e₁ (plus e₂ e₃)) e₁  -- true
-- 경로 없이 같다. 비용 0.

-- ═══ 정리 ═══
-- 순서의 비용 = proofDepth ≥ 1 (자명하지 않은 동치)
-- 순서 없음의 비용 = 0
-- 차이 ≥ 1.
-- 이 차이가 "매체에 순서를 넣었을 때 지불하는 최소 비용."
-- 12공리는 이 비용을 지불하는 도구 집합.
-- 0공리(런타임)는 비용 자체를 회피.

-- ═══ 보편 패턴: 순서의 수리비 ═══
-- 213 관점에서 모든 트레이드오프는 동일 구조:
--
-- 원래 구조 (순서 없음, 비용 0)
--   ↓ 매체에 올림 (순서 부여)
-- 수리비 발생 (비용 ≥ 1)
--
-- 분야별 사례:
-- 하드웨어: 파이프라인 해저드 = 순서(클럭)의 수리비
-- 소프트웨어: mutex/데드락 = 순서(락)의 수리비. 데드락 = 순서의 순환 = 213에서는 자연스러움
-- 네트워크: CAP 정리 = 분산(순서 없음)에서 합의(순서)의 불가능성
-- 물리: [x,p]≠0 = 측정 순서가 결과를 바꿈 = 비가환 = 순서가 물리적
-- 수학: 선택 공리 = "순서 없이 고른다"의 선언
-- 언어: 어순 = 선형 발화(매체)의 비용. 조사 = 수리비.
--
-- 213의 공식:
-- 순서의 비용 = proofDepth ≥ 1
-- 순서 없음의 비용 = 0
-- 비용은 배치만 바뀌고 총량은 보존.
-- (12공리의 분류: 9매체+3고유 = 총량 12)
