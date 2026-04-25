# 79 — Universal property of HasDistinguishing category

`Research/SemanticAtom.lean` 에 추가 된 `universalMorphism_unique`
+ `raw_initial`.  `RawInitiality.Lens.initiality` 의 HasDistinguishing-
level 재진술.

## 결과

```lean
theorem universalMorphism_unique (α : Type) [d : HasDistinguishing α]
    (f : Raw → α) (ha : f Raw.a = d.a) (hb : f Raw.b = d.b)
    (hslash : ∀ x y h, f (Raw.slash x y h) = d.combine (f x) (f y)) :
    ∀ r, f r = universalMorphism α r

theorem raw_initial (α : Type) [d : HasDistinguishing α] :
    ∃ f : Raw → α,
      (f Raw.a = d.a) ∧ (f Raw.b = d.b) ∧
      (∀ x y h, f (Raw.slash x y h) = d.combine (f x) (f y)) ∧
      (∀ g, ... → g = f)
```

## 의의

**Raw = initial object in HasDistinguishing category**.

- 임의 distinguishing framework α 에 대해, distinguishing-preserving
  함수 Raw → α 가 정확히 하나 (= `universalMorphism α`).
- 즉 213 axiom 이 *모든* 의미 framework 의 minimum 의 categorical
  명시.

## 4 direction 통합 의 완성

| Direction | Statement | Lean module |
|-----------|----------|-------------|
| Positive | `HasDistinguishing` typeclass + Raw instance | SemanticAtom |
| Self-application | Prop 의 instance (Xor + Iff) | SemanticAtom |
| Negative | `exists_non_lens_expressible` | SemanticAtom |
| Closure | `lens_canonical_universal` | LensCanonicalForm |
| **Universal property** | **`raw_initial` (∃ + uniqueness)** | **SemanticAtom** |

5 direction 모두 [propext, Quot.sound] only or no axioms — 의미
atom thesis 의 formal evidence 의 *categorical 완성*.

## RawInitiality 와 의 관계

`RawInitiality.Lens.initiality` 가 Lens-level universal property.
이번 결과 가 HasDistinguishing-level — 더 abstract.

차이:
- RawInitiality: "Lens 에 대해 view 가 unique homomorphism" (Lens
  carrier 의 closure).
- SemanticAtom.raw_initial: "HasDistinguishing instance 에 대해
  universalMorphism 이 unique" (의미 framework 의 abstract).

전자 는 Lens 의 정의 에 ad-hoc.  후자 가 abstract typeclass 위.
같은 universal property 의 두 layer.

## Axiom 검증

`#print axioms`:
- `universalMorphism_unique`: [propext]
- `raw_initial`: [propext, Quot.sound]

## Note 75-78 와 의 관계

- 75: thesis (semantic atom).
- 76: positive (Prop instance).
- 77: negative (boundary).
- 78: closure (canonical form).
- **79** (이): universal property (categorical 완성).

5 note 가 의미 atom thesis 의 formal evidence 의 통합.
Phenomenon 의 mathematically complete picture.

## 변경 이력

- 2026-04-25: SemanticAtom.lean 에 universalMorphism_unique +
  raw_initial 추가.  의미 atom thesis 의 categorical 완성.
