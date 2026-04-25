# 81 — Reach dichotomy: surjective vs non-surjective instances

`Research/InstanceReach.lean` 확장.  이전 (note 80) 의 non-
surjective witness (Fin 3) 의 dual: surjective instance (Bool)
+ image 의 closure properties.

## 결과

### Surjective: Bool instance

```lean
instance boolHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  combine := and
  ...

theorem bool_image_surjective :
  ∀ b : Bool, ∃ r : Raw, universalMorphism Bool r = b
```

Bool 의 carrier 가 두 base (true, false) 로 *완전 cover* —
combine 가 새 element 부재.

### Closure properties (image 의 minimum 성질)

```lean
theorem image_contains_a : ∃ r, universalMorphism α r = d.a
theorem image_contains_b : ∃ r, universalMorphism α r = d.b
theorem image_closed_under_distinct_combine (rx ry : Raw) (h : rx ≠ ry) :
  ∃ r, universalMorphism α r = d.combine (universalMorphism α rx) (universalMorphism α ry)
```

- Image 가 항상 a, b 를 포함.
- Image 가 *distinct Raw witnesses* 의 combine 위 closed.

## 의의 — Dichotomy

| Instance | Image | Surjective? |
|---------|-------|------------|
| **Bool** (and combine) | {true, false} = carrier | ✓ Surjective |
| **Fin 3** (constant 0 combine) | {0, 1} ⊊ {0, 1, 2} | ✗ Non-surjective |
| **Raw** (자기 자신) | Raw 전체 | ✓ (자명 surjective) |

Surjectivity 가 instance 의 specific 한 property — combine 의
generative power 에 의존.

## 의미 atom thesis 의 sharpening

Reach 의 dichotomy:
- **Surjective instance**: Raw 가 carrier 의 full generator.
  (e.g., Bool, Raw 자체.)
- **Non-surjective instance**: Carrier 가 image 보다 큼 — instance
  의 carrier 위 "unreachable" element 가 있음.  (e.g., Fin 3.)

이 dichotomy 가 framework 의 boundary 의 정확 한 형식:
- 모든 의미 framework 가 Raw 의 *image* 로 cover (note 80 의 reach
  부분).
- 하지만 carrier 의 full coverage 는 instance-specific.

## Image 의 minimum 표현

Image 가 항상:
1. d.a, d.b 포함.
2. Distinct Raw witnesses 의 combine 위 closed.

→ Image 가 framework 의 *minimum sub-instance* — 가장 작은
distinguishing-closed subset of α containing d.a, d.b.

## ZFC 와 의 정확 한 차이

ZFC 의 임의 set: 모든 element 가 axiom 으로 commit, 임의 의
"unreachable" 도 set 의 element.

213 framework: instance 의 carrier 가 임의 (Lean 의 type α),
하지만 *의미 의 reach* 는 image 만.  carrier 의 unreachable
element 는 framework 의 의미 generator 외부.

→ 의미 atom = Raw, 의미 의 reach = image, instance carrier 가
optional-extra.

## Axiom 검증

`#print axioms`:
- `bool_image_surjective`: no axioms.
- `image_contains_a`, `_b`: no axioms.
- `image_closed_under_distinct_combine`: [propext].

Lean 4 core baseline.  대부분 axiom 부재 (pure constructive).

## Note 75-80 와 의 관계

| Note | Direction |
|------|-----------|
| 75 | Conceptual thesis. |
| 76 | Self-application (Prop instance). |
| 77 | Function-level boundary. |
| 78 | Lens-level closure. |
| 79 | Categorical universal property. |
| 80 | Carrier vs reach (non-surjective witness). |
| **81** (이) | **Dichotomy** + image 의 closure properties. |

7 angle 모두 의미 atom thesis 의 evidence.

## 변경 이력

- 2026-04-25: InstanceReach.lean 확장.  Bool surjective +
  image closure properties.  reach dichotomy 의 형식 명시.
