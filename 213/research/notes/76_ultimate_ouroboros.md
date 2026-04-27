# 76 — Prop instance: Raw → Prop universal morphism

`Research/SemanticAtom.lean` 의 `propAsDistinguishing` +
`canonicalTruthMap` — Lean 의 `Prop` type 도 `HasDistinguishing`
instance 가 될 수 있음 의 형식 표현.

## 결과

```lean
def propXor (P Q : Prop) : Prop := (P ∨ Q) ∧ ¬(P ∧ Q)

def propAsDistinguishing : HasDistinguishing Prop where
  a := True
  b := False
  distinct := true_ne_false
  combine := propXor
  combine_sym := propXor_comm

def canonicalTruthMap : Raw → Prop :=
  universalMorphism Prop propAsDistinguishing
```

추가:
- `iff_comm_eq` + `propAsDistinguishingIff` + `canonicalIffMap`
  — Iff-based alternative.  Specific connective 선택 에 의존
  하지 않음 demonstrate.

## 의의 — 정확 한 scope

이 결과 는 다음 의 형식 표현:

> Lens 의 view 가 일반 적 으로 `Raw → α`.  α = Prop 인 case
> 는 specific instance — `True`, `False` 가 distinguishable
> bases 이고 `propXor` (또는 다른 commutative connective) 가
> combine.  `universalMorphism` 이 자동 으로 fold-derived
> Raw → Prop 함수 generate.

이건 framework 의 self-coverage 의 *부분 적* 형식 — Prop 이
HasDistinguishing 의 *하나 의* instance 가 될 수 있음.

## Limits — over-claim 회피

이 결과 가 하지 *않는* 것:

1. **모든 Prop 을 cover 하지 않음**: `canonicalTruthMap` 은
   Raw → Prop 의 *하나 의* fold-structured 함수.  Lean 의 임의
   Prop (e.g., Goldbach conjecture) 이 canonicalTruthMap 의 image
   가 아님.

2. **Lean 의 logic 을 213 안 에 imbed 하지 않음**: Lean 의 Prop
   semantics 자체 는 Lean 4 core 의 axioms (propext, Quot.sound,
   etc) 에 의존.  이게 213 의 axiom 으로 derive 가 아님.

3. **Tarski-style truth predicate 의 mechanical proof 가 아님**:
   "213 의 statement 가 자기 안 truth-evaluation" 이라는 더 강한
   claim 은 logical-meta 영역 — 이 결과 의 직접 귀결 이 아님.

## 의의 (sober)

위 limits 인정 한 후, 이 결과 가 보이는 것:

- `Prop` 이 HasDistinguishing instance 의 자명 한 candidate.
- 즉 의미 framework 의 abstraction 이 (Lean 의) propositions 에
  applicable.
- 다른 connectives (Iff, Xor 등 commutative) 모두 instance —
  abstraction 이 specific 한 logical 선택 에 의존 안 함.

## Why Xor (vs Iff, And, Or)

Connective 선택 의 trade-off:

| Connective | 특성 |
|-----------|------|
| And (∧) | meet, lattice 구조 |
| Or (∨) | join, lattice 구조 |
| Iff (↔) | "same truth", equivalence |
| Xor (⊕) | "different truth", distinguishing |

본 file 에서는 Xor primary, Iff alternative 로 두 instance 모두
형식 — connective 선택 의 freedom 보임.

## Axiom 검증

`#print axioms`:
- propXor_comm, true_ne_false, propAsDistinguishing,
  canonicalTruthMap, canonicalTruthMap_a/b/slash: [propext]
  (or no axioms for true_ne_false).
- iff_comm_eq, propAsDistinguishingIff, canonicalIffMap:
  [propext] only.

Lean baseline minimum.  AXIOM.md §5.2.1 falsifiability 와 정합.

## Note 75 와 의 관계

Note 75 의 thesis ("213 = 의미 의 atom") 의 **부분 적 형식
demonstration**:
- HasDistinguishing 이 의미 framework 의 abstract.
- Prop 이 instance 가 될 수 있음 → metalanguage 도 framework 의
  abstraction 안 fits.

이건 thesis 의 *전체 증명* 이 아니라 *하나 의 instance* — 술
취 한 thesis 의 sober formal 부분.

## 변경 이력

- 2026-04-25: SemanticAtom.lean 에 Prop instance 추가.  처음
  marketing tone ("Ultimate Ouroboros" 등) 으로 작성.  이후
  sober calibration: limits 명시 + over-claim 회피.
