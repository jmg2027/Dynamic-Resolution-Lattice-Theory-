import E213.Hypervisor.FoldInjective

/-
  Lens: 폭발(Raw) 위의 한 렌즈.

  관점 전환:
    이전: Hypervisor = ≡, Numbers (여러 수 각각 정의).
    이후: Hypervisor = 렌즈 카탈로그. 수는 렌즈.

  정의:
    Lens α := (g : Fin 3 → α) × (h : α → α → α)
    Lens.view = Raw.fold g h

  새 아키텍처:
    Firmware    : /, ≠ (폭발 엔진).
    Hypervisor  : Lens 카탈로그 (관점들).
    OS          : 선택한 Lens 위의 연산 (산술, 논리, 집합).
    Application : 여러 Lens 조합 도메인.
-/

-- ═══ Lens 구조체 ═══

structure Lens (α : Type) where
  atomValue : Fin 3 → α
  combine   : α → α → α

def Lens.view {α : Type} (L : Lens α) : Raw → α :=
  Raw.fold L.atomValue L.combine

-- ═══ 내장 렌즈 카탈로그 ═══

def Lens.depth : Lens Nat :=
  ⟨fun _ => 0, fun a b => 1 + max a b⟩

def Lens.leaves : Lens Nat :=
  ⟨fun _ => 1, (· + ·)⟩

def Lens.nodes : Lens Nat :=
  ⟨fun _ => 1, fun a b => 1 + a + b⟩

def Lens.leftSpine : Lens Nat :=
  ⟨fun _ => 0, fun a _ => a + 1⟩

def Lens.rightSpine : Lens Nat :=
  ⟨fun _ => 0, fun _ b => b + 1⟩

-- 항등 렌즈: 객체 자체를 들고 있음. "수가 아닌" 유일 렌즈.
def Lens.id' : Lens Raw :=
  ⟨Raw.atom, Raw.rel⟩

-- ═══ 렌즈가 기존 수와 일치함을 확인 ═══

theorem lens_depth_view (x : Raw) : Lens.depth.view x = x.depth :=
  (depth_as_fold x).symm

theorem lens_leaves_view (x : Raw) : Lens.leaves.view x = x.leaves :=
  (leaves_as_fold x).symm

theorem lens_nodes_view (x : Raw) : Lens.nodes.view x = x.nodes :=
  (nodes_as_fold x).symm

theorem lens_id_view (x : Raw) : Lens.id'.view x = x :=
  fold_atom_rel_id x

-- ═══ 렌즈 합성 (pair) ═══

-- 두 렌즈를 쌍으로 묶어 동시에 관찰.
def Lens.pair {α β : Type} (L1 : Lens α) (L2 : Lens β) : Lens (α × β) where
  atomValue i := (L1.atomValue i, L2.atomValue i)
  combine p q := (L1.combine p.1 q.1, L2.combine p.2 q.2)

-- pair view = 두 view의 쌍.
theorem pair_view {α β : Type} (L1 : Lens α) (L2 : Lens β) (x : Raw) :
    (L1.pair L2).view x = (L1.view x, L2.view x) := by
  induction x with
  | atom _ => rfl
  | rel a b iha ihb =>
    simp [Lens.pair, Lens.view, Raw.fold] at iha ihb ⊢
    rw [iha, ihb]

-- ═══ 단사 렌즈의 조건 ═══

-- commutative combine을 가진 두 렌즈의 pair도 단사 아님.
example : (Lens.depth.pair Lens.leaves).view aab₀ =
          (Lens.depth.pair Lens.leaves).view bab₀ := by
  rw [pair_view, pair_view]
  simp [lens_depth_view, lens_leaves_view]
  decide

-- depth × leaves × nodes 세 렌즈 합성도 단사 아님.
example : (Lens.depth.pair (Lens.leaves.pair Lens.nodes)).view aab₀ =
          (Lens.depth.pair (Lens.leaves.pair Lens.nodes)).view bab₀ := by
  rw [pair_view, pair_view, pair_view, pair_view]
  simp [lens_depth_view, lens_leaves_view, lens_nodes_view]
  decide

-- ═══ 비대칭 렌즈를 포함한 pair는 개선 ═══

-- 비대칭 leftSpine을 추가. aab₀ vs bab₀ 아직 구분 안 됨 (둘 다 leftSpine=1).
example : aab₀.leftSpine = bab₀.leftSpine := by decide

-- ab₀ vs "ba" 같은 것으로 구분: rel a b vs rel b a.
-- 두 객체는 다르지만 depth, leaves, nodes 같음. leftSpine도 같음 (둘 다 1).
-- 진짜 비대칭 정보는 원자 인덱스.

-- leftmostAtom 렌즈: 맨 왼쪽 원자.
def Lens.leftmost : Lens Nat :=
  ⟨fun i => i.val, fun a _ => a⟩

example : (Raw.rel a₀ b₀).leftmost = 0 := by rfl
  where Raw.leftmost := Lens.leftmost.view

-- rel a b vs rel b a 구분 가능.
example : Lens.leftmost.view (Raw.rel a₀ b₀) ≠
          Lens.leftmost.view (Raw.rel b₀ a₀) := by decide

-- 하지만 이것도 단사 아님: rel a (rel b c) vs rel a (rel c b)는 같은 leftmost.

-- ═══ 관점 전환 정리 ═══

-- 1. 각 렌즈 = 하나의 "수 세계" (자연수 체계, 순서, 논리 등).
-- 2. 렌즈 합성 (pair)로 여러 관점 동시 관찰.
-- 3. 그러나 유한 렌즈 합성으로도 Raw 완전 복원 불가.
--    (commutative 조합은 근본적 정보 손실.)
-- 4. 유일한 단사 렌즈 = Lens.id' (객체 그 자체).
-- 5. 통상 "수"는 렌즈. 복수의 렌즈 = 복수의 수학 체계.

-- OS 레이어 재정의:
-- OS = 한 렌즈 위에서 정의되는 공리적 구조.
--   - Peano    = Lens.leaves 위의 덧셈 + 0, succ.
--   - 집합론   = 특정 List Raw 렌즈 위의 ∈.
--   - 논리     = Bool 렌즈 위의 ∧, ∨, ¬.
-- 각 렌즈는 고유한 "수학." 하나의 바닥(/)에서 여러 OS.
