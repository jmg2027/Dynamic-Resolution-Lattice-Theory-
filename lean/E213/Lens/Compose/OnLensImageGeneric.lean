import E213.Lens.Compose.OnLens
import E213.Lens.EqPW

/-!
# LensOnLensImageGeneric: generic Lens-on-Lens collapse

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

namespace E213.Lens.Compose.OnLensImageGeneric

open E213.Theory E213.Lens
open E213.Lens.Foundations.SemanticAtom
open E213.Lens.Compose.OnLens

/-- `lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b)`. -/
theorem lensCombineGeneric_const {α : Type} (c : α → α → α) (a b : α) :
    lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b) := by
  unfold lensCombineGeneric constLens; rfl


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

/-- **Generic tower collapse**: for any `α` with HasDistinguishing,
    the Lens-on-Lens universalMorphism factors through α via constLens —
    up to the `Lens α` reading-sameness (`sameLens d.same`).  ∅-axiom: the
    `lensHasDistinguishing` instance is itself pointwise (`sameLens`), so
    `universalMorphism_unique` carries no `funext`/`propext`.

    Generalizes `LensOnLensImage` (Bool case) — regardless of type α, the image
    of `Lens α` is the constLens pullback of the image of `α`. -/
theorem lensUniversalMorphism_factors_generic
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    (lensHasDistinguishing α).same
      (@universalMorphism (Lens α) (lensHasDistinguishing α) r)
      (constComposite α r) :=
  (lensHasDistinguishing α).same_symm
    (@universalMorphism_unique (Lens α) (lensHasDistinguishing α)
      (constComposite α)
      ((lensHasDistinguishing α).same_refl _)
      ((lensHasDistinguishing α).same_refl _)
      (fun x y h =>
        ⟨universalMorphism_slash α x y h, universalMorphism_slash α x y h,
         fun _ _ => universalMorphism_slash α x y h⟩)
      r)

end E213.Lens.Compose.OnLensImageGeneric
