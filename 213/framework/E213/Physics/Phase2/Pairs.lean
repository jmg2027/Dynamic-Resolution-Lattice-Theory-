import E213.Physics.Phase2.Existence

/-!
# Phase 2 Pairs — 쌍의 정보 구조

Origin: *d=5*. Shape: *5 vertex, (3,2), 10 쌍*. Existence: *5 무엇 + 분류*.
이 파일: *그 10 쌍 사이에 무엇이 있는가?*

## 쌍 = 두 vertex의 *서수 무관* 조합

  pair (i, j) with i ≠ j.  C(5, 2) = 10 가능 pair.

  block 분류 따라:
    - **AA pair**: 둘 다 big block (3개의 무엇 중 2 선택).  C(3,2)=3.
    - **BB pair**: 둘 다 small block.  C(2,2) = 1.
    - **AB pair**: cross (big × small).  3·2 = 6.

  Total: 3 + 1 + 6 = 10 ✓ (Shape.lean과 일관)

## 자연 발생하는 *bipartite* 구조

10 쌍 중 *6개가 cross (AB)*.  이 6개가 K_{3,2} bipartite 그래프
edge 집합.

  ★ Bipartite graph K_{NS,NT}^{(c=2)}는 axiom-derived ★
  단순 산술 사실: 3 vertex × 2 vertex = 6 cross pair.
  Phase 1의 PhotonKernel 작업도 이 bipartite 위였음.

## 형식 명제

  - PairAA, PairAB, PairBB 분류 function 정의
  - 각 분류의 cardinality decide-checked
  - Total 10 일관성

본 파일은 *axiom-free* — Existence + Shape 결과의 자연 귀결.
-/

namespace E213.Physics.Phase2.Pairs

open E213.Physics.Phase2.Existence

/-- 두 vertex의 쌍 정보가 어느 분류인지.
    AA: 둘 다 big block.  BB: 둘 다 small.  AB: cross. -/
inductive PairType
  | AA  -- big-big (within big block)
  | BB  -- small-small (within small block)
  | AB  -- cross (big-small or small-big)
  deriving DecidableEq, Repr

/-- 쌍 분류: 두 vertex 의 block 정보로부터. -/
def classifyPair (i j : Vertex) : PairType :=
  match inBigBlock i, inBigBlock j with
  | true,  true  => PairType.AA
  | false, false => PairType.BB
  | _,     _     => PairType.AB

/-- 모든 unordered pair (i, j) with i.val < j.val. -/
def allPairs : List (Vertex × Vertex) :=
  (List.finRange 5).flatMap (fun i =>
    (List.finRange 5).filterMap (fun j =>
      if i.val < j.val then some (i, j) else none))

/-- 쌍 총 개수 = 10. -/
theorem total_pairs_eq_10 : allPairs.length = 10 := by decide

/-- AA 쌍 (big-big) 개수 = 3. -/
theorem AA_pairs_count :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AA)).length = 3 := by
  decide

/-- BB 쌍 (small-small) 개수 = 1. -/
theorem BB_pairs_count :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.BB)).length = 1 := by
  decide

/-- AB 쌍 (cross) 개수 = 6.  K_{3,2} bipartite edge 수. -/
theorem AB_pairs_count :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AB)).length = 6 := by
  decide

/-- 모든 쌍이 AA, BB, AB 셋 중 하나로 분류 (exhaustive). -/
theorem AA_BB_AB_sum :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AA)).length
    + (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.BB)).length
    + (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AB)).length
    = allPairs.length := by decide

/-- ★ Phase 2 Pairs — 쌍 분류 종합 ★

  10 쌍 = 3 (AA) + 1 (BB) + 6 (AB).
  AB 6개가 *bipartite K_{3,2} 자연 발생*.
  
  Phase 1 PhotonKernel의 K_{NS,NT}^{(c)} 도 이 위에서 doubled. -/
theorem cosmos_pair_structure :
    -- AA: 3 (big block 내부)
    ((allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AA)).length = 3)
    -- BB: 1 (small block 내부)
    ∧ ((allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.BB)).length = 1)
    -- AB: 6 (bipartite edges)
    ∧ ((allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AB)).length = 6)
    -- Total 10
    ∧ (allPairs.length = 10) := by decide

end E213.Physics.Phase2.Pairs
