# 84 — Nat surjective: infinite carrier 의 reach 완성

`Research/InstanceReach.lean` 확장.  이전 (note 80, 81) 의 partial
result (small witnesses) 의 완성:

> ∀ n : Nat, ∃ r : Raw, universalMorphism Nat r = n.

## 결과

```lean
theorem nat_surjective_with_form : ∀ n : Nat, ∃ r : Raw,
    universalMorphism Nat r = n ∧
    (r = Raw.a ∨ ∃ x y h, r = Raw.slash x y h)

theorem nat_image_surjective :
    ∀ n : Nat, ∃ r : Raw, universalMorphism Nat r = n
```

## Construction

Witness via induction on n with form invariant:
- n = 0: r = Raw.a, form = Raw.a.
- n + 1: r' from IH (universalMorphism = n, form = a or slash).
  - r' ≠ Raw.b 가 form invariant 로 derived (helper:
    `natWitness_ne_b_helper`).
  - r := Raw.slash Raw.b r' (Raw.b ≠ r').
  - universalMorphism = 1 + n = n + 1 (combine = +).

Helper `natWitness_ne_b_helper` 가 form invariant (Raw.a 또는
slash) 로부터 r ≠ Raw.b 도출.  Slash form 은 `slash_ne_b` (depth-
based) 로 처리.

## Catalogue 완성

| Instance | Carrier | Image | Surjective? | Note |
|---------|---------|-------|------------|------|
| Bool (and) | finite | {true, false} | ✓ | 81 |
| Fin 3 (const) | finite | {0, 1} ⊊ {0,1,2} | ✗ | 80 |
| Nat (+) | infinite | Nat 전체 | **✓** | **84 (이)** |
| Raw (smart slash) | infinite | Raw 자체 | ✓ trivial | - |

→ 4 instance 의 reach 의 다양 한 case demonstration.

## 의의

**Infinite surjective**: Nat 같은 무한 carrier 도 Raw 의 image
로 *완전* covered.  의미 atom thesis 의 강한 evidence — Raw 의
generative power 가 무한 cardinality 의 framework 를 cover.

대조 (note 80): Fin 3 같은 *finite* instance 가 non-surjective
가능 (combine 의 generative power 부족).

**Image 의 cardinality 가 instance 의 specific algebraic property
에 의존** — 이게 framework 의 reach 의 정확 한 characterization.

## Axiom 검증

`#print axioms`:
- `nat_surjective_with_form`: [propext, Quot.sound]
- `nat_image_surjective`: [propext, Quot.sound]

Lean 4 core baseline.  Classical / LEM 부재.

## 변경 이력

- 2026-04-25: nat_image_surjective 완전 증명.  helpers (slash_ne_a,
  slash_ne_b, natWitness_ne_b_helper) 도입 — depth-based discriminator
  로 Raw 의 inequality 도출.  catalogue 의 infinite surjective case
  완성.
