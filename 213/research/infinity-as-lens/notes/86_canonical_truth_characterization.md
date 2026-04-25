# 86 — canonicalTruthMap 의 정확 한 characterization

`Research/CanonicalTruthChar.lean` 신규.

## Question

`SemanticAtom.canonicalTruthMap : Raw → Prop` (Xor-based Prop
instance 의 universal morphism) 의 의미 가 정확 히 무엇 인가?

## Answer

> `canonicalTruthMap r ↔ a-count of r is odd`.

즉 Prop instance 의 universal morphism 이 *Raw 의 a-count
parity* 를 추출.

## 결과

```lean
def aCountParityLens : Lens Bool := ⟨true, false, fun x y => xor x y⟩

theorem canonicalTruthMap_iff_aCountOdd (r : Raw) :
  canonicalTruthMap r ↔ aCountParityLens.view r = true
```

aCountParityLens: a → true, b → false, combine = Bool xor.
canonicalTruthMap (Prop, Xor) ↔ aCountParityLens (Bool, xor) —
같은 information 의 Prop / Bool 의 dual.

## Verification

```
- a (1 a): canonicalTruthMap = True, parity = true (odd)  ✓
- b (1 b): canonicalTruthMap = False, parity = false (even) ✓
- a/b (1 a, 1 b): True XOR False = True, parity = T XOR F = true ✓
- a/(a/b) (2 a, 1 b): True XOR True = False, parity = T XOR T = false ✓
```

## 의의

**의미 atom 의 self-application 의 정확 한 *내용***:

이전 (note 76) 의 self-application: Prop 이 instance 가 될 수
있음.  
이번 (note 86): 그 instance 의 universal morphism 이 *정확 히*
a-count parity — 의미 의 atom 의 self-evaluation 이 specific
algebraic invariant.

→ Prop instance 가 trivial 한 self-application 가 아니라 의미
있는 *measurement* — Raw 의 a-count parity 를 추출.

## Connection to other characterizations

framework 안 의 다른 Lens 들 도 specific algebraic invariant 추출:
- `Lens.leaves` (Lens Nat): a + b count.
- `Lens.depth` (Lens Nat): tree depth.
- `parityLens` (Lens Bool, 다른 구성): leaves count parity.
- `boolXorLens` (Lens Bool): some XOR variant.
- `abLens` (Lens (Nat × Nat)): (a-count, b-count).
- **`aCountParityLens` (Lens Bool, 이 file)**: a-count parity
  specifically.
- **`canonicalTruthMap` (Raw → Prop)**: 같은 정보 의 Prop form.

→ 같은 framework 의 여러 Lens 가 다른 algebraic invariant 추출.
canonicalTruthMap 이 그 중 specific 한 instance.

## Self-cover thesis 의 sharpening

note 75-76 의 self-cover claim ("Prop 이 framework 의 instance"):
이번 결과 가 더 sharp form — *어떤* Prop 의 universal morphism
이 정확 히 a-count parity.  Self-application 이 trivially
"Prop 이 instance" 가 아니라 *specific algebraic content* 를
가지고 있음.

이게 framework 의 self-cover 의 정확 한 의미: Prop 의 instance
가 specific 한 invariant (a-count parity) 추출 → self-knowledge
의 specific content.

## Axiom 검증

`#print axioms`:
- `aCountParityLens_slash`: [propext]
- `propXor_iff_bool_xor`: [propext]
- `canonicalTruthMap_iff_aCountOdd`: [propext]

Lean 4 core baseline.

## 변경 이력

- 2026-04-25: CanonicalTruthChar.lean 작성.  canonicalTruthMap 의
  정확 한 characterization (a-count parity).  self-application 의
  specific algebraic content 명시.
