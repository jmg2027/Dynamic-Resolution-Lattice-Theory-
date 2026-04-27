import E213.Research.LensOnLens

/-!
# Research.LensOnLensImageGeneric: generic Lens-on-Lens collapse

`LensOnLensImage` 의 Bool 특수 case 를 generic α 로 일반화.

## 핵심

For any `α` with `HasDistinguishing` instance,
`@universalMorphism (Lens α) (lensHasDistinguishing α)`
factors through `α`:

```
        Raw
       /   \
universalMorphism α        lensUniversalMorphism α
       ↓                    ↓
       α  ─── constLens ───→ Lens α
```

즉 `Lens α` 의 universalMorphism image 는 `α` 의 image
의 constLens-pullback — recursive Lens^n α tower 의 모든
level 에 서 동일 한 collapse 발생.
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

/-- **Generic tower collapse**: For any `α` with HasDistinguishing,
    the Lens-on-Lens universalMorphism factors through α via
    constLens.

    `LensOnLensImage` (Bool case) 의 일반화 — α 가 어떤 type 이든
    `Lens α` 의 image 는 `α` 의 image 의 constLens-pullback. -/
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
