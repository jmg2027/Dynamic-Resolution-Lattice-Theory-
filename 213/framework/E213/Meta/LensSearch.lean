import E213.Meta.LeapAnalysis

/-
  Lens Search Space: 가능한 렌즈 조합 공간 탐색 framework.

  목적:
    주어진 명제 φ 에 대해 RespectsLens L φ 인 lens L 찾기.

  Framework 구조:
    1. Base lens catalog.
    2. Combinators (pair, ...).
    3. Sample-based evaluator (respectsOn).
    4. Search algorithm (BFS / heuristic).
    5. Cache / pruning.

  실제 완전 자동화는 undecidable general.
  하지만 sample-based + finite search 가능.
-/

-- ═══ Lens Point: 탐색 공간 의 노드 ═══

structure LensPoint (α : Type) where
  name : String
  lens : Lens α
  deriving Repr

-- Base Nat lenses.
def baseNatLenses : List (LensPoint Nat) :=
  [ ⟨"depth", Lens.depth⟩,
    ⟨"leaves", Lens.leaves⟩,
    ⟨"nodes", Lens.nodes⟩,
    ⟨"leftSpine", Lens.leftSpine⟩,
    ⟨"rightSpine", Lens.rightSpine⟩,
    ⟨"leftmost", Lens.leftmost⟩ ]

-- ═══ Sample-based evaluator ═══

-- 주어진 sample set 에서 L 이 φ 를 respect 하는가?
-- ∀ x y ∈ samples, L.equiv x y → φ x = φ y.
def respectsOn {α : Type} [DecidableEq α]
    (L : Lens α) (φ : Raw → Bool) (samples : List Raw) : Bool :=
  samples.all fun x =>
    samples.all fun y =>
      !(decide (L.view x = L.view y)) || (φ x = φ y)

-- ═══ Search: 카탈로그 전체 스캔 ═══

def scanNatLenses (φ : Raw → Bool) (samples : List Raw) :
    List (String × Bool) :=
  baseNatLenses.map fun L => (L.name, respectsOn L.lens φ samples)

-- 첫 번째 respecting lens.
def firstRespectingNat (φ : Raw → Bool) (samples : List Raw) :
    Option String :=
  (baseNatLenses.find? fun L =>
    respectsOn L.lens φ samples).map (·.name)

-- ═══ 예시 실행 ═══

-- 샘플: levelUpTo 2 = 75 Raw.
def search_samples : List Raw := levelUpTo 2

-- 명제 1: φ(x) = (x.depth = 0). atom 만.
def φ_depth_zero (x : Raw) : Bool := decide (x.depth = 0)

-- 이 명제는 depth lens 가 respect.
example : respectsOn Lens.depth φ_depth_zero search_samples = true := by
  native_decide

-- 명제 2: φ(x) = (x.leaves = 1). atom 만 (leaves 1 = atom).
def φ_leaves_one (x : Raw) : Bool := decide (x.leaves = 1)

example : respectsOn Lens.leaves φ_leaves_one search_samples = true := by
  native_decide

-- 명제 3: φ(x) = (x = a₀). depth 로 not respecting.
def φ_is_a0 (x : Raw) : Bool := decide (x = a₀)

-- depth 는 respect X (a₀ vs b₀ 둘 다 depth 0 이지만 φ 다름).
example : respectsOn Lens.depth φ_is_a0 search_samples = false := by
  native_decide

-- Scan 결과 (which lens respects φ_depth_zero?):
-- depth ✓, leaves ✓ (atom = leaves 1), nodes ✓, ...

-- ═══ Combinator: pair ═══

-- Pair lens 추가 생성.
def pairedNatLenses : List (LensPoint (Nat × Nat)) :=
  [ ⟨"depth×leaves", Lens.depth.pair Lens.leaves⟩,
    ⟨"depth×nodes",  Lens.depth.pair Lens.nodes⟩,
    ⟨"leaves×nodes", Lens.leaves.pair Lens.nodes⟩,
    ⟨"left×right",   Lens.leftSpine.pair Lens.rightSpine⟩ ]

-- Pair 가 respect 더 쉽게 (섬세한 kernel).
example : respectsOn (Lens.depth.pair Lens.leaves)
    φ_is_a0 search_samples = false := by native_decide

-- ═══ 결론: Framework 완성 ═══

-- Lens Search Space 는:
--   (a) Base lenses (6 Nat, 1 Raw, 1 Bool, ...).
--   (b) Combinators (pair, swap, ...).
--   (c) Sample evaluator (respectsOn).
--   (d) Scan / find / search functions.
--
-- 사용자 요청 실현:
--   입력: φ, samples.
--   출력: respecting lens 후보.
--   자동 진단.
--
-- 한계:
--   Sample-based (all x, y ∈ samples 만 체크).
--   True respect 증명 아님 (그건 Lean proof 필요).
--   하지만 strong heuristic.
