import E213.Research.IdentityLens

/-!
# Research.UniverseFlat: 213 self-reference 의 universe-flat 성

213 의 self-reference (idLens, Raw.eval) 는 universe ascent
부재.

## 형식 정리

`every_lens_factors_through_idLens`: 임의 Lens L 의 view 가
idLens.view 를 통해 factor — 즉 L.view = g ∘ idLens.view for
some g.  Yoneda-like.

이것이 idLens 가 Raw 의 **complete Lens-observable description**
임의 의미.

## 213 vocabulary

- 일반 type theory: Type : Type 1 strict, universe hierarchy 강제.
- 213: Raw → Lens Raw → Raw (idLens 의 cycle) 가 single universe
  안에서 작동.  추가 ascent 부재.
- 모든 다른 Lens 가 idLens 를 통해 factor (Yoneda 성).

self-reference 가 framework 내장.
-/

namespace E213.Research.UniverseFlat

open E213.Firmware E213.Hypervisor E213.Research.IdentityLens

/-- **Yoneda-like factoring**: 모든 Lens L 의 view 가 idLens.view
    를 통해 factor.  즉 L.view r = (L.view) (idLens.view r). -/
theorem every_lens_factors_through_idLens {α : Type} (L : Lens α) :
    ∀ r : Raw, L.view r = L.view (idLens.view r) := by
  intro r
  rw [idLens_is_id r]

/-- Sharp form: g := L.view, then L.view = g ∘ idLens.view. -/
theorem factoring_formula {α : Type} (L : Lens α) :
    L.view = L.view ∘ idLens.view := by
  funext r
  exact every_lens_factors_through_idLens L r

/-- **idLens 가 ⊥ (refines preorder 의 bottom)**: 모든 Lens L 에
    대해 idLens.refines L.  즉 idLens 가 가장 finer Lens. -/
theorem idLens_is_bottom {α : Type} (L : Lens α) :
    idLens.refines L := by
  intro r r' h
  show L.view r = L.view r'
  have hview : idLens.view r = idLens.view r' := h
  rw [idLens_is_id r, idLens_is_id r'] at hview
  rw [hview]

end E213.Research.UniverseFlat
