import E213.Hypervisor.Quotient

/-
  Meta: Lens 는 범주 (Category) 구조.

  Objects: Lens α (각 α).
  Morphisms L → M: L.refines M (kernel 섬세함 순서).

  구조:
    1. Preorder: refines 는 refl, trans.
    2. Initial (∀ L, id' → L): Lens.id'.
    3. Terminal (∀ L, L → constTrue): Lens.constTrue.
    4. Product: Lens.pair L M.
       - pair → L, pair → M 프로젝션.
       - universal property (N → L, N → M → N → pair).

  이 범주 = 수학 분야들의 relation category.
    각 object = 공리계 ("Set 에서 같다", "위상에서 같다", ...).
    각 morphism = 한 공리계 → 다른 공리계 refinement.
-/

-- ═══ Preorder 구조 ═══

theorem Lens.refines_refl {α : Type} (L : Lens α) : L.refines L :=
  fun _ _ h => h

theorem Lens.refines_trans {α β γ : Type}
    {L : Lens α} {M : Lens β} {N : Lens γ} :
    L.refines M → M.refines N → L.refines N :=
  fun h1 h2 x y h => h2 x y (h1 x y h)

-- ═══ Extrema ═══

-- Initial: id' 이 모든 L 로 refine (이미 증명됨, Lens.id_refines_all).
-- Terminal: constTrue 가 모든 L 의 refinement (Lens.refines_constTrue).

example : ∀ {α : Type} (L : Lens α), Lens.id'.refines L :=
  @Lens.id_refines_all

example : ∀ {α : Type} (L : Lens α), L.refines Lens.constTrue :=
  @Lens.refines_constTrue

-- ═══ Product: Lens.pair 의 projections ═══

-- pair L M → L.
theorem Lens.pair_refines_left {α β : Type}
    (L : Lens α) (M : Lens β) : (L.pair M).refines L := by
  intro x y h
  show L.view x = L.view y
  have hpair : (L.pair M).view x = (L.pair M).view y := h
  rw [pair_view, pair_view] at hpair
  exact (Prod.mk.injEq _ _ _ _).mp hpair |>.1

-- pair L M → M.
theorem Lens.pair_refines_right {α β : Type}
    (L : Lens α) (M : Lens β) : (L.pair M).refines M := by
  intro x y h
  show M.view x = M.view y
  have hpair : (L.pair M).view x = (L.pair M).view y := h
  rw [pair_view, pair_view] at hpair
  exact (Prod.mk.injEq _ _ _ _).mp hpair |>.2

-- ═══ Product universal property ═══

-- N → L 과 N → M 이 있으면 유일한 N → pair L M 존재.
theorem Lens.pair_universal {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (hL : N.refines L) (hM : N.refines M) :
    N.refines (L.pair M) := by
  intro x y h
  show (L.pair M).view x = (L.pair M).view y
  rw [pair_view, pair_view]
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨hL x y h, hM x y h⟩

-- ═══ 해석 ═══

-- 이 범주 (LensCat) 는 수학 분야들의 refinement 구조.
-- Objects: 각 공리계 (= 렌즈).
-- Morphisms: 한 공리계가 다른 것을 refine (더 섬세한 구별 제공).
-- Initial: id' = "모든 것을 구별" (Raw 자체).
-- Terminal: constTrue = "아무것도 구별 안 함" (Unit).

-- Lens.pair = Cartesian product.
-- 두 공리계의 정보 를 동시에 관찰하는 "결합 공리계."
-- 예: depth × leaves = 깊이 + 잎 수 공동 관찰.

-- ═══ 구체 예: depth × leaves > depth ═══

-- pair 가 각 component 보다 섬세 (refine):
example : (Lens.depth.pair Lens.leaves).refines Lens.depth :=
  Lens.pair_refines_left _ _

example : (Lens.depth.pair Lens.leaves).refines Lens.leaves :=
  Lens.pair_refines_right _ _

-- 다른 섬세 렌즈가 depth 와 leaves 둘 다 refine 하면 pair 도 refine.
example (N : Lens Nat)
    (hL : N.refines Lens.depth) (hM : N.refines Lens.leaves) :
    N.refines (Lens.depth.pair Lens.leaves) :=
  Lens.pair_universal _ _ _ hL hM

-- ═══ 통합 그림 ═══

-- 모든 공리계가 형성하는 lattice:
--
--                id' (Raw, 무한, 모든 것 구별)
--                 │
--           ┌─────┼─────┐
--           │     │     │
--      depth × leaves ×...  (각 pair)
--           │     │     │
--          depth  leaves  atomSet  ...
--           │     │     │
--           └──┬──┴──┬──┘
--              │     │
--         truthValue │
--              │     │
--           constTrue (모두 같음)
--
-- 위로 갈수록 섬세, 아래로 갈수록 거침.
-- 각 수학 분야 = 이 lattice 의 한 점.
