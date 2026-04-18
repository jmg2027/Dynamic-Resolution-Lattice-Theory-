import E213.Applications.HomeoExamples

/-
  Category Functor 구체 예시.

  LensCat:
    Objects: Lens α.
    Morphisms L → M: L.refines M.

  Functor 예시:
    Pair-functor: L ↦ L.pair X for fixed X.
    Id-functor: 항등.
-/

-- ═══ Id functor ═══

-- F(L) = L. 자명한 identity functor.

-- CF_001: id functor object 보존.
theorem cf_001 {α : Type} (L : Lens α) : id L = L := rfl

-- CF_002: id functor morphism 보존.
theorem cf_002 {α β : Type} {L : Lens α} {M : Lens β}
    (hLM : L.refines M) : (id L).refines (id M) := hLM

-- ═══ Pair-functor ═══

-- 고정 X 에 대해: F_X (L) := L.pair X.
-- Morphism: L.refines M → (L.pair X).refines (M.pair X).

theorem cf_003 {α β γ : Type} (X : Lens γ) {L : Lens α} {M : Lens β}
    (hLM : L.refines M) : (L.pair X).refines (M.pair X) := by
  intro x y h
  show (M.pair X).view x = (M.pair X).view y
  rw [pair_view, pair_view] at h ⊢
  have h1 : L.view x = L.view y := (Prod.mk.injEq _ _ _ _).mp h |>.1
  have h2 : X.view x = X.view y := (Prod.mk.injEq _ _ _ _).mp h |>.2
  have hM : M.view x = M.view y := hLM x y h1
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨hM, h2⟩

-- ═══ Natural transformation 예시 ═══

-- pair L M → pair M L: kernel 등가.
theorem cf_004 {α β : Type} (L : Lens α) (M : Lens β) (x y : Raw) :
    (L.pair M).equiv x y ↔ (M.pair L).equiv x y := by
  unfold Lens.equiv
  rw [pair_view, pair_view, pair_view, pair_view]
  constructor
  · intro h
    have h1 := (Prod.mk.injEq _ _ _ _).mp h
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h1.2, h1.1⟩
  · intro h
    have h1 := (Prod.mk.injEq _ _ _ _).mp h
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h1.2, h1.1⟩

-- ═══ Composition (3-pair) ═══

theorem cf_005 {α β γ : Type} (L : Lens α) (M : Lens β) (N : Lens γ) :
    ((L.pair M).pair N).refines L := by
  intro x y h
  have h1 : (L.pair M).view x = (L.pair M).view y :=
    Lens.pair_refines_left (L.pair M) N _ _ h
  exact Lens.pair_refines_left L M _ _ h1

-- ═══ LensCat 요약 ═══
-- Object: Lens α (관점).
-- Morphism: refines (kernel 섬세도).
-- Identity: refines_refl.
-- Composition: refines_trans.
-- Initial: Lens.id' (가장 섬세).
-- Terminal: Lens.constTrue (가장 거침).
-- Product: Lens.pair.
-- Natural trans: pair commutativity (cf_004).
