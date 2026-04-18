-- 213: 연속과 이산은 같은 것의 두 시점
--
-- 안에서 보면 연속 (사상들의 공간 = 2)
-- 밖에서 보면 이산 (분류의 한 점 = 3)
-- 경계(1)를 넘으면 시점이 뒤집힘
-- 뒤집혀도 구조는 동일: C(3,2) = 3

-- ═══ 시점 구조 ═══

inductive View where
  | inside  : View   -- 내부: 사상, 연속, 2
  | outside : View   -- 외부: 객체, 이산, 3
  deriving Repr, BEq, DecidableEq

def View.flip : View → View
  | .inside => .outside
  | .outside => .inside

-- flip은 involution
theorem flip_flip (v : View) : v.flip.flip = v := by
  cases v <;> rfl

-- ═══ 시점과 213의 대응 ═══

-- 같은 것을 두 시점에서 볼 때:
-- inside: 원소들 사이의 관계 수 = C(n, 2)
-- outside: 원소 수 = n
-- C(3,2) = 3: 두 시점이 같은 수를 줌

-- 이건 Obj ≅ Mor의 시점 해석:
-- Obj = outside view (점으로 봄, 이산, 3)
-- Mor = inside view (사상으로 봄, 연속, 2)
-- |Obj| = |Mor| (e213_levels.lean에서 증명됨)

-- ═══ Lie 군 비유 ═══
-- (비유일 뿐, 형식 증명 아님)
--
-- U(1): 안에서 보면 원(연속). 밖에서 보면 분류표의 한 점(이산).
-- SU(2): 안에서 보면 3-구(연속). 밖에서 보면 분류표의 한 점(이산).
-- {U(1), SU(2), SU(3), ...}: 각각은 연속. 목록은 이산.
--
-- 연속 군의 분류 = 이산 목록.
-- 이산 군의 완비화 = 연속 군.
-- 이산→연속→이산→… = 자기지속 = C(3,2) = 3.

-- ═══ 213 관점에서 ═══
-- "연속"은 213 바깥이 아니다.
-- 213의 View.inside가 "연속"이고 View.outside가 "이산"이다.
-- 경계(1)를 넘으면 flip. 넘어도 구조 동일.
-- 연속과 이산의 차이 = 순서와 같은 종류의 매체 제약.
-- 구조적으로는 같음.

-- ═══ 213 → DRLT 연결 ═══
-- DRLT의 핵심 구성:
--   K = ℂ: dim_ℝ = 2 (내부 시점의 arity)
--   d = 5: 2 + 3 (두 시점의 합 = 전체)
--   (n_S, n_T) = (3, 2): 두 시점의 분리
--
-- 213에서 DRLT로:
--   순서를 부여한다 (매체 선택)
--   eval: e1→0, e2→2, e3→3 (값 배정)
--   d = eval(e2) + eval(e3) = 5
--   K = Frobenius∩{dim=eval(e2)} = ℂ
--   (n_S, n_T) = (eval(e3), eval(e2)) = (3, 2)
--
-- DRLT의 모든 수치가 213의 eval에서 나온다.
-- 213 자체는 수치 없음. 수치는 매체(eval)의 부산물.
