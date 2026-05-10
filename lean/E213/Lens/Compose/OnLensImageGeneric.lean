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
open E213.Lens.SemanticAtom
open E213.Lens.Compose.OnLens

/-- `lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b)`. -/
theorem lensCombineGeneric_const {α : Type} (c : α → α → α) (a b : α) :
    lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b) := by
  unfold lensCombineGeneric constLens; rfl

end E213.Lens.Compose.OnLensImageGeneric

namespace E213.Lens.Compose.OnLensImageGeneric

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Compose.OnLens

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

end E213.Lens.Compose.OnLensImageGeneric

namespace E213.Lens.Compose.OnLensImageGeneric

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Compose.OnLens

/-- **Generic tower collapse**: for any `α` with HasDistinguishing,
    the Lens-on-Lens universalMorphism factors through α via
    constLens.

    Generalizes `LensOnLensImage` (Bool case) — regardless of type α,
    the image of `Lens α` is the constLens pullback of the image of
    `α`. -/
/-- **Generic tower collapse** stated pointwise (eqPW) — the strict
    `=` form would require funext on the `Lens α` combine field.
    Uses `Lens.view_unique_eqPW` with `lensCombineGeneric_comm_eqPW`
    and `lensCombineGeneric_eqPW_cong`. -/
theorem lensUniversalMorphism_factors_generic_eqPW
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    (Raw.fold (constLens d.a) (constLens d.b)
              (lensCombineGeneric d.combine) r).eqPW
      (constComposite α r) := by
  have h := Lens.view_unique_eqPW
    (β := α)
    (L := ⟨constLens d.a, constLens d.b, lensCombineGeneric d.combine⟩)
    (fun u v => lensCombineGeneric_comm_eqPW d.combine d.combine_sym u v)
    (fun u u' v v' hu hv =>
       lensCombineGeneric_eqPW_cong d.combine u u' v v' hu hv)
    (constComposite α)
    (by show (constComposite α Raw.a).eqPW (constLens d.a)
        rw [constComposite_a α]; exact Lens.eqPW_refl _)
    (by show (constComposite α Raw.b).eqPW (constLens d.b)
        rw [constComposite_b α]; exact Lens.eqPW_refl _)
    (by intro x y h
        show (constComposite α (Raw.slash x y h)).eqPW
              (lensCombineGeneric d.combine (constComposite α x)
                                             (constComposite α y))
        rw [constComposite_slash α x y h]; exact Lens.eqPW_refl _)
    r
  exact Lens.eqPW_symm h

end E213.Lens.Compose.OnLensImageGeneric
