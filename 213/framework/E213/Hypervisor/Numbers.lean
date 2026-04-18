import E213.Firmware.Reachable

/-
  5가지 "수" 비교.

  / 에서 나오는 자연수의 여러 경로:
    1. depth : 트리 높이 = / 겹침 횟수 (시간).
    2. leaves: 잎 개수 = 원자 사용 횟수 (재료).
    3. nodes : 전체 노드 = atom + rel 수 (크기).
    4. 경로수: 단사성(v3_injective)으로 항상 1 (trivial).
    5. Level : levelUpTo n의 length (전역 우주 크기).

  각각 다른 자연수. 모두 0-free parameter로 / 에서 도출.
-/

-- ═══ 정의 ═══

-- 방법 2: leaves (잎 = 원자 등장 횟수, 재사용 포함).
def Raw.leaves : Raw → Nat
  | .atom _  => 1
  | .rel x y => x.leaves + y.leaves

-- 방법 5: nodes (전체 노드 = atom + rel 수).
def Raw.nodes : Raw → Nat
  | .atom _  => 1
  | .rel x y => 1 + x.nodes + y.nodes

-- 방법 1: depth는 이미 RawAxiomV3.lean에 있음.
-- 방법 3: levelUpTo는 Reachable.lean에 있음.
-- 방법 4: 경로수는 단사성으로 trivial. 아래 주석 참고.

-- ═══ 구체 예시: a/b ═══

example : ab₀.depth  = 1 := by decide
example : ab₀.leaves = 2 := by decide
example : ab₀.nodes  = 3 := by decide

-- ═══ 구체 예시: a/(a/b) ═══
-- 사용자 주장: depth=2, leaves=2, nodes=4.
-- 실제 재귀 정의로: depth=2, leaves=3, nodes=5.
-- leaves=2, nodes=4는 "고유 원소 수" 기준이지 트리 기준 아님.

example : aab₀.depth  = 2 := by decide  -- 사용자 ✓
example : aab₀.leaves = 3 := by decide  -- 사용자 2와 다름
example : aab₀.nodes  = 5 := by decide  -- 사용자 4와 다름

-- 확인: a/(a/b) = rel a (rel a b). 트리:
--        rel
--        / \
--       a  rel
--          / \
--         a   b
-- leaves(트리) = 3 (a가 두 번, b 한 번).
-- nodes(트리)  = 5 (2 rel + 3 atom occurrence).
-- depth        = 2 (가장 긴 루트-잎 경로).

-- ═══ 관계 1: 이진 트리 항등식 ═══

-- 모든 Raw는 완전 이진 트리 → nodes = 2·leaves - 1.
-- 안전하게 양변 + 1 형태로.
theorem nodes_succ_eq_two_leaves (x : Raw) :
    x.nodes + 1 = 2 * x.leaves := by
  induction x with
  | atom i => simp [Raw.nodes, Raw.leaves]
  | rel a b iha ihb =>
    simp [Raw.nodes, Raw.leaves]
    omega

-- 따름: leaves ≥ 1.
theorem leaves_pos (x : Raw) : 0 < x.leaves := by
  induction x with
  | atom i => simp [Raw.leaves]
  | rel a b iha _ => simp [Raw.leaves]; omega

-- ═══ 관계 2: depth < leaves (트리 모양 부등식) ═══

theorem depth_lt_leaves (x : Raw) : x.depth < x.leaves := by
  induction x with
  | atom i => simp [Raw.depth, Raw.leaves]
  | rel a b iha ihb =>
    simp [Raw.depth, Raw.leaves]
    omega

-- ═══ 사용자 기준: 고유 서브트리 / 고유 원자 ═══

-- 사용자의 leaves=2(a/(a/b)) = 고유 원자 수 {a, b}.
-- 사용자의 nodes=4 = 고유 서브트리 수 {a, b, a/b, a/(a/b)}.
-- 트리 기준(재귀)과 다른 "수." 집합론적.

def Raw.subtrees : Raw → List Raw
  | .atom i  => [.atom i]
  | .rel a b => (.rel a b) :: (a.subtrees ++ b.subtrees)

def Raw.atomsUsed : Raw → List Raw
  | .atom i  => [.atom i]
  | .rel a b => a.atomsUsed ++ b.atomsUsed

def Raw.distinctSubtrees (x : Raw) : Nat := x.subtrees.dedup.length
def Raw.distinctAtoms    (x : Raw) : Nat := x.atomsUsed.dedup.length

-- 검증: 사용자 예시값 재현.
example : aab₀.distinctSubtrees = 4 := by decide  -- 사용자 nodes=4 ✓
example : aab₀.distinctAtoms    = 2 := by decide  -- 사용자 leaves=2 ✓
example : ab₀.distinctSubtrees  = 3 := by decide
example : ab₀.distinctAtoms     = 2 := by decide

-- 요약:
-- 재귀 트리 기준: depth=2, leaves=3, nodes=5 (a/(a/b)).
-- 집합 기준:    distinctAtoms=2, distinctSubtrees=4.
-- 같은 객체, 다른 "수." 어느 쪽이 옳은가? 둘 다 자연수.
-- 무엇을 세느냐의 차이. / 에서 내장된 구별 가능한 수는 여럿.

-- ═══ 경로수 (방법 4): 단사성으로 trivial ═══

-- v3_injective: slash x y h = slash x' y' h' → x = x' ∧ y = y'.
-- 따라서 Reachable한 rel x y를 만드는 slash 경로는 유일.
-- "경로수"는 모든 Reachable에 대해 1. 흥미롭지 않음.

-- ═══ Level count (방법 3): Reachable.lean ═══

-- |levelUpTo 0| = 3,  |levelUpTo 1| = 9,  |levelUpTo 2| = 75.
-- 전역 성질. 우주 크기. local 트리 성질(1,2,5)과 구분됨.

-- ═══ 종합표 (a/(a/b) 기준) ═══
-- 방법 1 depth              = 2   (시간)
-- 방법 2 leaves (트리)      = 3   (원자 occurrence)
-- 방법 2' distinctAtoms     = 2   (원자 종류)
-- 방법 5 nodes (트리)       = 5   (총 occurrence)
-- 방법 5' distinctSubtrees  = 4   (서브트리 종류)
-- 방법 4 경로수             = 1   (단사성)
-- 방법 3 Level count        = 75  (Level 2 전체)
