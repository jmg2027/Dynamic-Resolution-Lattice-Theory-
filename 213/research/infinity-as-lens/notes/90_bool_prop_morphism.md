# 90 — Bool → Prop morphism: functorial commutativity

`Research/BoolPropMorphism.lean` 신규.  `Bool` 과 `Prop` 의
HasDistinguishing instance 사이 의 morphism + functoriality.

## 결과

```lean
def boolToProp (b : Bool) : Prop := b = true

theorem boolToProp_true : boolToProp true = True
theorem boolToProp_false : boolToProp false = False
theorem boolToProp_and (x y : Bool) :
  boolToProp (Bool.and x y) = (boolToProp x ∧ boolToProp y)

theorem universalMorphism_commute (r : Raw) :
  @universalMorphism Prop propAsDistinguishingAnd r
    = boolToProp (universalMorphism Bool r)
```

[propext] only.

## 의의

**Functoriality**: 같은 Raw 의 두 universal morphism (Bool, Prop)
이 boolToProp 으로 commute.

`universalMorphism Prop = boolToProp ∘ universalMorphism Bool`.

→ 두 framework instance 간 의 *structure-preserving* relationship —
`Bool` (combine = and) 의 universal morphism 이 `Prop` (combine =
And) 의 universal morphism 의 Bool form.

## DistMorphism 와 의 관계

`DistMorphism Bool Prop` 의 instance — typeclass synthesis 부재
때문 explicit 정의 부재.  대신 직접 record (`boolToProp_*`
theorems) + functoriality theorem 으로 명시.

## Self-application 의 multi-instance commutativity

| Source instance | Morphism | Target instance |
|----------------|----------|-----------------|
| Bool (and) | boolToProp | Prop (And) |
| Bool (xor)? | boolToProp_xor? | Prop (Xor)? |

(Bool 의 다른 instance 도 정의 가능 — Bool with xor 등.)

이번 결과 가 *And-And* dual 만 형식 — 다른 connective pair 의
commutativity 도 가능 한 axis (incremental).

## 의미 atom 의 instance lattice

framework 안 의 multiple instance:
- Raw (자명).
- Bool (and combine).
- Prop (And, Or, Xor, Iff combine — 4 variants).
- Fin 3, Nat, Int (Nat-typed).

**Cross-instance morphisms** 의 commutativity 가 framework 의
internal 구조 의 일관성 의 evidence.

## Axiom 검증

`#print axioms`:
- `universalMorphism_commute`: [propext]

## 변경 이력

- 2026-04-25: BoolPropMorphism.lean 신규.  Bool ↔ Prop morphism
  + functorial commutativity.  의미 framework 의 instance lattice
  내부 의 structural relationship 의 명시.
