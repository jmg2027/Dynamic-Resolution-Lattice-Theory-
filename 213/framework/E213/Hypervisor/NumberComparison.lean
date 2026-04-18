import E213.Hypervisor.Numbers

/-
  depth / leaves / nodes 성질 비교.

  같은 Raw에서 세 수를 뽑지만, 성질은 다름.

  핵심 차이 (slash x y 아래 변환):
    depth  = 1 + max(x, y)     ← max 기준
    leaves =      x + y        ← 순수 가법
    nodes  = 1 + (x + y)       ← affine 가법

  결과:
    depth : 느리게 자람 (log 규모).
    leaves: 선형 자람 (재료의 합).
    nodes : 선형 자람 (leaves와 affine 관계).
-/

-- ═══ Slash 변환 법칙 ═══

theorem depth_slash (x y : Raw) (h : x ≠ y) :
    (slash x y h).depth = 1 + max x.depth y.depth := by
  simp [slash, Raw.depth]

theorem leaves_slash (x y : Raw) (h : x ≠ y) :
    (slash x y h).leaves = x.leaves + y.leaves := by
  simp [slash, Raw.leaves]

theorem nodes_slash (x y : Raw) (h : x ≠ y) :
    (slash x y h).nodes = 1 + x.nodes + y.nodes := by
  simp [slash, Raw.nodes]

-- ═══ 좌우 대칭성 ═══

-- 객체 rel x y ≠ rel y x (diff_inputs_diff_output).
-- 하지만 세 수는 모두 대칭.

theorem depth_comm (x y : Raw) :
    (Raw.rel x y).depth = (Raw.rel y x).depth := by
  simp [Raw.depth, Nat.max_comm]

theorem leaves_comm (x y : Raw) :
    (Raw.rel x y).leaves = (Raw.rel y x).leaves := by
  simp [Raw.leaves, Nat.add_comm]

theorem nodes_comm (x y : Raw) :
    (Raw.rel x y).nodes = (Raw.rel y x).nodes := by
  simp [Raw.nodes]; omega

-- 의미: 수는 순서를 기억 못 함. 객체는 기억함.

-- ═══ 정보 손실 (non-injectivity) ═══

-- 세 수를 모두 합쳐도 객체를 복원 못 함.
-- 반례: aab₀ ≠ bab₀ 이지만 모든 수가 같음.

example : aab₀ ≠ bab₀ := by decide
example : aab₀.depth  = bab₀.depth  := by decide
example : aab₀.leaves = bab₀.leaves := by decide
example : aab₀.nodes  = bab₀.nodes  := by decide

-- 수는 함수 Raw → Nat. 단사가 아님.
-- 객체 → 수: 정보 잃음. 수 → 객체: 복원 불가.

-- ═══ 증가 방식의 수량적 차이 ═══

-- atom에서 시작하여 n번 / 를 자기 자신과 합칠 때 (불가하지만 trade):
-- depth  : 0 → 1 → 2 → ... → n     (+1 매번)
-- leaves : 1 → 2 → 4 → ... → 2ⁿ    (×2 매번, 대칭 합 가정)
-- nodes  : 1 → 3 → 7 → ... → 2ⁿ⁺¹-1 (지수 폭발)
-- depth는 로그 규모, 나머지는 지수 규모.

-- 구체 확인:
example : a₀.depth = 0 ∧ a₀.leaves = 1 ∧ a₀.nodes = 1 := by decide
example : ab₀.depth = 1 ∧ ab₀.leaves = 2 ∧ ab₀.nodes = 3 := by decide

-- 깊이 1당 잎/노드는 2배로 커질 수 있음 (max 증가분 = 1, 합 증가분은 제약없음).

-- ═══ 지수 상한: leaves ≤ 2^depth ═══

-- depth d인 Raw는 leaves가 최대 2^d.
-- depth는 느림 (log 규모), leaves는 빠름 (exp 상한).
theorem leaves_le_two_pow_depth (x : Raw) : x.leaves ≤ 2 ^ x.depth := by
  induction x with
  | atom i => simp [Raw.leaves, Raw.depth]
  | rel a b iha ihb =>
    simp [Raw.leaves, Raw.depth, pow_succ]
    have h1 : a.leaves ≤ 2 ^ (max a.depth b.depth) :=
      iha.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    have h2 : b.leaves ≤ 2 ^ (max a.depth b.depth) :=
      ihb.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    omega

-- ═══ 종합: 세 수의 성질 ═══
-- | 성질          | depth     | leaves      | nodes        |
-- |--------------|-----------|-------------|--------------|
-- | slash 변환   | 1+max     | x+y         | 1+x+y        |
-- | 좌우 대칭    | ✓         | ✓           | ✓            |
-- | 단사 (객체→) | ✗         | ✗           | ✗            |
-- | 최소값 (atom)| 0         | 1           | 1            |
-- | 성장 규모   | log        | 최대 exp    | 최대 exp     |
-- | 상호 관계    | <leaves   | nodes=2L-1  | nodes=2L-1   |

-- 결론:
-- depth는 "시간" (로그, max).
-- leaves는 "재료" (선형 합, 지수 상한).
-- nodes는 "크기" (leaves와 affine linked).
-- 세 수 다 같은 성질이 아니라, 다른 측면을 봄.
