# 87 — 두 Prop instance 의 distinguished morphism

`Research/CanonicalTruthChar.lean` 확장.  Note 76 의 dual instance
(Xor + Iff) 가 *다른* universal morphism 임 의 명시.

## 결과

```lean
theorem canonicalTruthMap_ne_canonicalIffMap_witness :
  canonicalTruthMap (Raw.slash Raw.a Raw.b (by decide))
    ≠ canonicalIffMap (Raw.slash Raw.a Raw.b (by decide))

theorem canonicalTruthMap_ne_canonicalIffMap :
  canonicalTruthMap ≠ canonicalIffMap
```

Witness: `Raw.slash Raw.a Raw.b _`.
- canonicalTruthMap (Xor): propXor True False = True (XOR).
- canonicalIffMap (Iff): True ↔ False = False.

→ 두 morphism 의 image 가 specific Raw 에서 다름.

## 의의 — connective 의 freedom 의 명시

Note 76 의 sober claim: "Prop 이 *하나 의* HasDistinguishing
instance 만 가지지 않음 — 다른 commutative connective 도 instance".

이번 결과 가 그 freedom 의 *형식 적 evidence*: Xor 와 Iff 가
정말 *다른* universal morphism 을 만든다.  단순 한 statement 가
아니라 specific witness 가 있는 inequality.

## Self-application 의 sharpening

이전 (note 86): canonicalTruthMap (Xor) = a-count parity 의
정확 한 content.

이번 (note 87): canonicalIffMap (Iff) ≠ canonicalTruthMap (Xor)
— 다른 Prop instance 의 morphism 이 different algebraic invariant
추출.

→ self-application 의 *multiple* algebraic instances 가능.  framework
의 self-cover 가 specific connective 에 의존 — Xor 와 Iff 모두
valid 하지만 *다른* invariant 추출.

## Connective 의 algebraic content

|Connective | Universal morphism = | Algebraic invariant |
|----------|--------------------|---------------------|
| Xor (propXor) | canonicalTruthMap | a-count parity (note 86) |
| Iff (·↔·) | canonicalIffMap | b-count parity (interpretive) |
| And (∧) | (potential alternative) | both-true (가능) |
| Or (∨) | (potential alternative) | either-true (가능) |

각 commutative connective 가 framework 의 self-application 의
specific instance — 모두 valid, 다른 invariant.

## Axiom 검증

`#print axioms`:
- `iffBoolLens_slash`: [propext]
- `canonicalTruthMap_ne_canonicalIffMap_witness`: [propext]
- `canonicalTruthMap_ne_canonicalIffMap`: [propext]

Lean 4 core baseline.

## 변경 이력

- 2026-04-25: CanonicalTruthChar.lean 에 inequality witness 추가.
  Connective freedom 의 형식 evidence + self-application 의
  multiple instance demonstration.
