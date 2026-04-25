# 80 — 의미 generator 의 reach: instance carrier 의 boundary

`Research/InstanceReach.lean` 형식.  `universalMorphism α :
Raw → α` 의 image 가 *항상* α 와 같은 가? — 답: **아님**.

## 결과

```lean
instance fin3HasDistinguishing : HasDistinguishing (Fin 3) where
  a := 0
  b := 1
  combine _ _ := 0
  ...

theorem fin3_image_in_01 (r : Raw) :
  universalMorphism (Fin 3) r = 0 ∨ universalMorphism (Fin 3) r = 1

theorem fin3_image_strict :
  ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x
```

`Fin 3` instance: a := 0, b := 1, combine := λ _ _, 0.
- Reach: {0, 1} (a, b 만 직접, combine 의 모든 결과 가 0).
- Carrier: {0, 1, 2}.
- 2 ∉ image — strict subset.

## 의의 — 의미 atom thesis 의 sharpening

이전 의 thesis: "어떤 의미 framework 도 Raw 의 derivation".

Refinement (이 note):
- Raw 가 *minimum generator* — 모든 reach element 가 image.
- 하지만 instance 의 carrier 가 *image 보다 클* 수 있음.
- 즉 framework 의 carrier ≠ framework 의 reach.

**Reach** = "Raw 로 부터 reach 가능 한 element" = universalMorphism
의 image.  
**Carrier** = α 의 모든 element.

이 두 가지 의 차이 가 framework 의 boundary 의 또 하나 의 형식.

## Note 75-79 와 의 관계

| Direction | Boundary 표현 |
|-----------|--------------|
| 75 | Conceptual thesis |
| 76 | Positive (Prop instance) |
| 77 | Function-level boundary (∃ f, ¬ Lens-expressible) |
| 78 | Lens-level closure (canonical form) |
| 79 | Categorical universal property |
| **80** (이) | **Instance carrier vs reach** — α \ image 의 가능성 |

여섯 angle 모두 의미 atom thesis 의 instance.  Phenomenon 의
multifaceted picture.

## ZFC 와 의 비교

ZFC 의 임의 set: 모든 element 가 axiom 으로 commit.
213 framework: instance 의 carrier 가 임의 (Lean 의 type α),
하지만 reach 가 generator (Raw) 의 image.

→ 의미 atom 은 generator, instance 는 그 위 "unreachable" elements
가 가능 — ZFC 의 commitment 와 의 정확 한 차이.

## Axiom 검증

`#print axioms`:
- `fin3_image_in_01`: [propext]
- `fin3_image_strict`: [propext]

Lean 4 core baseline.  Quot.sound 도 부재.

## 변경 이력

- 2026-04-25: InstanceReach.lean 작성.  의미 generator 의 reach
  vs carrier 의 분리 의 형식 적 witness.
