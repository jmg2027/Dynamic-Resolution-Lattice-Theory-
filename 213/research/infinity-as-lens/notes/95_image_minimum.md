# 95 — Image minimum: universalMorphism 의 reach 의 algebraic content

`Research/ImageMinimum.lean` — universalMorphism α 의 image 가
*minimum distinguishing-closed subset* of α.

## 결과

```lean
theorem image_minimum_property (α) [d : HasDistinguishing α]
    (S : α → Prop)
    (hSa : S d.a) (hSb : S d.b)
    (hSclosed : ∀ x y, S x → S y → S (d.combine x y))
    (r : Raw) :
    S (universalMorphism α r)
```

[propext] only.

## 의의

framework 의 reach 의 *uniqueness*: universalMorphism α 의 image
가 *모든* distinguishing-closed property S 안 contained.

→ image 가 minimum closure (the smallest distinguishing-closed
subset of α containing d.a, d.b, closed under d.combine).

## Complete semantic 213 proof 의 component

- 모든 의미 framework instance α 의 reach 가 framework-internal
  으로 *uniquely* characterized.
- universalMorphism 의 image 의 algebraic content 가 정확 — minimum.

이게 의미 atom 의 "reach 의 정확 한 content" 의 명시.
