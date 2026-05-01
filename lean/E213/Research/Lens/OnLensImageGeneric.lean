import E213.Research.Lens.OnLens

/-!
# Research.LensOnLensImageGeneric: generic Lens-on-Lens collapse

Generalizes the Bool special case of `LensOnLensImage` to generic α.

## Core

For any `α` with a `HasDistinguishing` instance,
`@universalMorphism (Lens α) (lensHasDistinguishing α)`
factors through `α`:

```
        Raw
       /   \
universalMorphism α        lensUniversalMorphism α
       ↓                    ↓
       α  ─── constLens ───→ Lens α
```

That is, the universalMorphism image of `Lens α` is the constLens
pullback of the image of `α` — the same collapse occurs at every
level of the recursive Lens^n α tower.
-/

namespace E213.Research.LensOnLensImageGeneric

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens

/-- `lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b)`. -/
theorem lensCombineGeneric_const {α : Type} (c : α → α → α) (a b : α) :
    lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b) := by
  unfold lensCombineGeneric constLens; rfl

end E213.Research.LensOnLensImageGeneric

namespace E213.Research.LensOnLensImageGeneric

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens

/-- Composite map: Raw → α → Lens α via constLens. -/
def constComposite (α : Type) [d : HasDistinguishing α] : Raw → Lens α :=
  fun r => constLens (@universalMorphism α d r)

theorem constComposite_a (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.a = constLens d.a := by
  unfold constComposite
  rw [@universalMorphism_a α d]

theorem constComposite_b (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.b = constLens d.b := by
  unfold constComposite
  rw [@universalMorphism_b α d]

theorem constComposite_slash (α : Type) [d : HasDistinguishing α]
    (x y : Raw) (h : x ≠ y) :
    constComposite α (Raw.slash x y h) =
      lensCombineGeneric d.combine (constComposite α x) (constComposite α y) := by
  unfold constComposite
  rw [@universalMorphism_slash α d x y h]
  exact (lensCombineGeneric_const d.combine _ _).symm

end E213.Research.LensOnLensImageGeneric

namespace E213.Research.LensOnLensImageGeneric

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens

/-- **Generic tower collapse**: for any `α` with HasDistinguishing,
    the Lens-on-Lens universalMorphism factors through α via
    constLens.

    Generalizes `LensOnLensImage` (Bool case) — regardless of type α,
    the image of `Lens α` is the constLens pullback of the image of
    `α`. -/
theorem lensUniversalMorphism_factors_generic
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    @universalMorphism (Lens α) (lensHasDistinguishing α) r =
      constComposite α r := by
  have := @universalMorphism_unique (Lens α) (lensHasDistinguishing α)
    (constComposite α)
    (constComposite_a α)
    (constComposite_b α)
    (constComposite_slash α) r
  exact this.symm

end E213.Research.LensOnLensImageGeneric
