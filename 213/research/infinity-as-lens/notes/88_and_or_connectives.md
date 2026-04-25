# 88 — And-based Prop instance: degenerate combine

`Research/SemanticAtom.lean` + `CanonicalTruthChar.lean` 확장.
3번째 commutative connective (Xor, Iff 다음 의 And).

## 결과

```lean
def propAsDistinguishingAnd : HasDistinguishing Prop where
  a := True; b := False; combine := And; ...

def canonicalAndMap : Raw → Prop := universalMorphism Prop (...)

theorem canonicalAndMap_iff_eq_a (r : Raw) :
    canonicalAndMap r ↔ r = Raw.a
```

[propext, Quot.sound] only.

## Algebraic content: degenerate

And 가 *very weak* combine — `T ∧ F = F`, `T ∧ T = T`, `F ∧ F = F`.

→ Universal morphism 의 결과:
- a → T.
- b → F.
- slash x y → x ∧ y.  Both T iff both a (recursively).
- 하지만 slash 가 distinct (x ≠ y) — both a 부재 (slash a a 부재).
- 따라서 모든 slash 의 결과 = F.

**Degenerate algebraic content**: canonicalAndMap r = T iff r = Raw.a.

## Three Prop instances 의 algebraic invariants

| Connective | Universal morphism | Invariant |
|-----------|-------------------|-----------|
| Xor | canonicalTruthMap | a-count parity (note 86) |
| Iff | canonicalIffMap | b-count parity (note 87+) |
| **And** | **canonicalAndMap** | **r = Raw.a (이 note)** |

각 connective 가 *radically different* algebraic content:
- Xor: 분포 적 (every leaf 의 contribution).
- Iff: 분포 적 (XNOR fold).
- And: degenerate (only a-leaf 단일 case 가 T).

## 의의

Connective 의 generative power 의 spectrum:
- **Strong** (Xor, Iff): leaves 의 모든 정보 추출 (parity).
- **Weak** (And): 거의 모든 case 가 collapse (F).

같은 framework abstraction (HasDistinguishing) 안 의 다양 한
instance 가 *radically different* algebraic content carry.
self-application 의 freedom 이 강함.

## Or 도 비슷 가능?

Or: T ∨ F = T, T ∨ T = T, F ∨ F = F.  Dual to And.
Hypothesis: canonicalOrMap r ↔ r ≠ Raw.b (= ∃ a leaf in r).

(추가 가능 한 axis — 이 note 에서 not formalized.)

## Axiom 검증

- canonicalAndMap_iff_eq_a: [propext, Quot.sound]

## 변경 이력

- 2026-04-25: And-based instance + characterization.  Connective
  의 algebraic spectrum 명시 (strong: Xor/Iff, weak: And).
