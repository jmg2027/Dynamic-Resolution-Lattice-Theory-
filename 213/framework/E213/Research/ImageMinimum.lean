import E213.Research.SemanticAtom

/-!
# Research.ImageMinimum: universalMorphism image 의 minimum closure

framework 의 reach (universalMorphism α 의 image) 가 항상 α 의
*minimum distinguishing-closed subset* 임 의 형식.

## 결과

```lean
theorem image_minimum_property (α) [d : HasDistinguishing α]
    (S : α → Prop)
    (hSa : S d.a) (hSb : S d.b)
    (hSclosed : ∀ x y, S x → S y → S (d.combine x y)) :
    ∀ r : Raw, S (universalMorphism α r)
```

## 의의

framework 의 reach 의 정확 한 algebraic content:
- ∀ S : α → Prop with `d.a, d.b ∈ S` and `S` closed under combine,
  universalMorphism 의 image ⊆ S.
- 즉 image 가 *minimum* distinguishing-closed subset of α.
- → framework 의 reach 가 "distinguishable-closed sub-instance"
  의 strict minimum.

## Complete semantic 213 proof 의 component

User directive (2026-04-25): complete semantic proof 까지 멈추지
말 것.  이번 결과 가 그 proof 의 component:
- universalMorphism 의 image 가 *uniquely characterized* —
  minimum distinguishing-closed.
- 모든 의미 framework instance 의 reach 가 framework-internal
  으로 *uniquely* determined.
-/

namespace E213.Research.ImageMinimum

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Image minimum property**: `universalMorphism α` 의 image 가
    *모든* distinguishing-closed subset 안 contained.  즉 image 가
    minimum closure. -/
theorem image_minimum_property (α : Type) [d : HasDistinguishing α]
    (S : α → Prop)
    (hSa : S d.a) (hSb : S d.b)
    (hSclosed : ∀ x y, S x → S y → S (d.combine x y))
    (r : Raw) :
    S (universalMorphism α r) := by
  induction r using Raw.rec with
  | a =>
      rw [universalMorphism_a α]
      exact hSa
  | b =>
      rw [universalMorphism_b α]
      exact hSb
  | slash x y h ihx ihy =>
      rw [universalMorphism_slash α x y h]
      exact hSclosed _ _ ihx ihy

end E213.Research.ImageMinimum
