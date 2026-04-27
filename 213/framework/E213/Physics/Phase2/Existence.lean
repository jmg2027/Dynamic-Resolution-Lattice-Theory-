import E213.Physics.Phase2.Origin

/-!
# Phase 2 Existence — d=5에 *무엇*이 있는가?

Origin.lean: *우주는 d=5 차원*.
Shape.lean: *5 점, (3,2) 분할, 10 쌍*.
이 파일: *그 5는 무엇이며, 그 사이 정보는 무엇인가?*

## 213이 답할 수 있는 것 (그리고 못 하는 것)

### 답할 수 있는 것
- *5개의 무엇*이 있다 (Fin 5 type).
- 두 무엇 사이는 *같다 / 같지 않다* 의 답 (DecidableEq).
- 그 답들의 패턴이 *atomic partition* 따라 (3,2)로 분류됨.

### 213만으로는 못 하는 것
- 그 5 무엇의 *명칭*은 axiom에 없음 (Lens 추가 시 결정).
- 거리, 시간, 입자 등 *분류*도 axiom에 없음 (Lens 출력).
- "labels" (어느 게 spatial, 어느 게 temporal) 도 Lens 결정.
  단지 *block 크기* 만 axiom 결정.
-/

namespace E213.Physics.Phase2.Existence

/-- d=5 무엇 type — Fin 5.  최소 Lens output. -/
def Vertex : Type := Fin 5

/-- 두 무엇이 같은가는 *결정 가능*. -/
instance : DecidableEq Vertex := inferInstanceAs (DecidableEq (Fin 5))

/-- 어느 vertex가 "big block" (크기 3)에 속하는가 — block 0.
    Labels는 임의 (Lens 결정), 단지 size 만 axiom 결정. -/
def inBigBlock (v : Vertex) : Bool := v.val < 3

/-- "small block" (크기 2)에 속하는가 — 보완. -/
def inSmallBlock (v : Vertex) : Bool := decide (3 ≤ v.val)

/-- 모든 vertex는 정확히 한 block에 (mutually exclusive). -/
theorem block_disjoint_at_0 :
    inBigBlock ⟨0, by decide⟩ = !inSmallBlock ⟨0, by decide⟩ := by decide
theorem block_disjoint_at_1 :
    inBigBlock ⟨1, by decide⟩ = !inSmallBlock ⟨1, by decide⟩ := by decide
theorem block_disjoint_at_2 :
    inBigBlock ⟨2, by decide⟩ = !inSmallBlock ⟨2, by decide⟩ := by decide
theorem block_disjoint_at_3 :
    inBigBlock ⟨3, by decide⟩ = !inSmallBlock ⟨3, by decide⟩ := by decide
theorem block_disjoint_at_4 :
    inBigBlock ⟨4, by decide⟩ = !inSmallBlock ⟨4, by decide⟩ := by decide

/-- Big block 에 정확히 3 개 vertex. -/
theorem big_block_size_three :
    ((List.finRange 5).filter (fun v => inBigBlock v)).length = 3 := by
  decide

/-- Small block 에 정확히 2 개 vertex. -/
theorem small_block_size_two :
    ((List.finRange 5).filter (fun v => inSmallBlock v)).length = 2 := by
  decide

/-- 두 block 합이 5 (전체 vertex 개수). -/
theorem block_sizes_sum_to_5 :
    ((List.finRange 5).filter (fun v => inBigBlock v)).length
    + ((List.finRange 5).filter (fun v => inSmallBlock v)).length
    = 5 := by decide

/-- ★ Phase 2 Existence — 213이 답할 수 있는 모든 것 ★

  d=5 차원에 *5 vertex*가 있다.
  Atomic partition은 *(3, 2)* 크기로 갈라진다.
  더 이상의 ontology (이름, 의미)는 axiom 결정 안 함. -/
theorem cosmos_existence_minimal :
    -- (3, 2) block sizes
    (((List.finRange 5).filter (fun v => inBigBlock v)).length = 3)
    ∧ (((List.finRange 5).filter (fun v => inSmallBlock v)).length = 2)
    -- Sum to 5
    ∧ (((List.finRange 5).filter (fun v => inBigBlock v)).length
       + ((List.finRange 5).filter (fun v => inSmallBlock v)).length
       = 5) := by decide

end E213.Physics.Phase2.Existence
