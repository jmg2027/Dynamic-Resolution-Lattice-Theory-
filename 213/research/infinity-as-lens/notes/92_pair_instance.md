# 92 — Pair instance: categorical product of HasDistinguishing

`Research/PairInstance.lean` 신규.  두 HasDistinguishing instance
의 categorical product.

## 결과

```lean
def pairHasDistinguishing (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] : HasDistinguishing (α × β) where
  a := (d_α.a, d_β.a)
  b := (d_α.b, d_β.b)
  combine := fun p q => (d_α.combine p.1 q.1, d_β.combine p.2 q.2)
  ...

theorem universalMorphism_pair_commute (r : Raw) :
  @universalMorphism (α × β) (pairHasDistinguishing α β) r
    = (universalMorphism α r, universalMorphism β r)
```

[propext] only.

## 의의 — Categorical product

distinguishing-framework category 의 *binary product* 의
universal property:
- (α × β) 가 instance.
- universalMorphism (α × β) 가 components 별 split.
- 즉 Raw → α × β 가 (Raw → α) × (Raw → β) 로 induced.

이게 categorical product 의 정확 한 statement — Raw 의 의미
atom 으로 부터 product framework 가 자연스럽게 emerge.

## 다양 한 instance 의 product

Pair 로 새 instance 생성 가능:
- `Bool × Bool` (4 element carrier).
- `Bool × Nat` (mixed type).
- `Prop × Prop` (4 connective × 4 connective = 16 product).

같은 product 의 universal morphism 이 항상 components 별 split.

## 의미 atom thesis 의 closure properties

- Note 90: Cross-instance morphism (Bool ↔ Prop).
- Note 92 (이): Cross-instance product (α × β).

같은 framework 의 instance 들 이 *categorical operations* (morphism,
product) 위 closed — 의미 framework 의 self-contained categorical
structure.

## Axiom 검증

`#print axioms`:
- `universalMorphism_pair_commute`: [propext]

## 변경 이력

- 2026-04-25: PairInstance.lean 신규.  의미 framework 의
  categorical product 의 universal property.
