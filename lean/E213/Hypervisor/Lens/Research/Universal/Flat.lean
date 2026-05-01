import E213.Hypervisor.Lens.Research.Lens.Identity

/-!
# Research.UniverseFlat: universe-flat nature of 213 self-reference

213's self-reference (idLens, Raw.eval) has no universe ascent.

## Formal theorems

`every_lens_factors_through_idLens`: the view of any Lens L factors
through idLens.view — that is, L.view = g ∘ idLens.view for some g.
Yoneda-like.

This is the meaning of idLens being the **complete Lens-observable
description** of Raw.

## 213 vocabulary

- General type theory: Type : Type 1 strict, universe hierarchy forced.
- 213: Raw → Lens Raw → Raw (the idLens cycle) operates within a
  single universe.  No additional ascent.
- Every other Lens factors through idLens (Yoneda property).

Self-reference is built into the framework.
-/

namespace E213.Hypervisor.Lens.Research.Universal.Flat

open E213.Firmware E213.Hypervisor E213.Hypervisor.Lens.Research.Lens.Identity

/-- **Yoneda-like factoring**: the view of every Lens L factors through
    idLens.view.  That is, L.view r = (L.view) (idLens.view r). -/
theorem every_lens_factors_through_idLens {α : Type} (L : Lens α) :
    ∀ r : Raw, L.view r = L.view (idLens.view r) := by
  intro r
  rw [idLens_is_id r]

/-- Sharp form: g := L.view, then L.view = g ∘ idLens.view. -/
theorem factoring_formula {α : Type} (L : Lens α) :
    L.view = L.view ∘ idLens.view := by
  funext r
  exact every_lens_factors_through_idLens L r

/-- **idLens is ⊥ (bottom of the refines preorder)**: idLens.refines L
    for every Lens L.  That is, idLens is the finest Lens. -/
theorem idLens_is_bottom {α : Type} (L : Lens α) :
    idLens.refines L := by
  intro r r' h
  show L.view r = L.view r'
  have hview : idLens.view r = idLens.view r' := h
  rw [idLens_is_id r, idLens_is_id r'] at hview
  rw [hview]

end E213.Hypervisor.Lens.Research.Universal.Flat
