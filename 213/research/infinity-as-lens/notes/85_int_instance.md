# 85 — Int instance: infinite non-surjective carrier

`Research/InstanceReach.lean` 의 4번째 catalogue.

## 결과

```lean
instance intHasDistinguishing : HasDistinguishing Int where
  a := 0
  b := 1
  combine := (· + ·)
  ...

theorem int_image_nonneg (r : Raw) : 0 ≤ universalMorphism Int r
theorem int_image_strict :
  ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x  -- witness: -1
```

## 의의 — 4번째 case

| Instance | Carrier | Image | Surjective | 용도 |
|---------|---------|-------|------------|------|
| Bool (and) | finite | {true, false} | ✓ | finite surj |
| Fin 3 (const) | finite | {0, 1} ⊊ {0,1,2} | ✗ | finite non-surj |
| Nat (+) | infinite | Nat 전체 | ✓ | **infinite surj** (note 84) |
| **Int (+)** | **infinite** | **Nat (≥ 0) ⊊ Int** | **✗** | **infinite non-surj** (이) |
| Raw | infinite | Raw | ✓ trivial | reflexive |

5 instance 의 reach behavior 의 *complete dichotomy*:
- finite × {surj, non-surj}.
- infinite × {surj, non-surj}.
- (Raw 가 trivial reflexive.)

## 핵심 통찰

**infinite cardinality 가 surjective 를 보장 안 함**.  Int 처럼
combine 의 monotonic generative property (positive-only) 가 negative
부분 unreachable 로 만듦.

→ "Reach = image" 가 cardinality 가 아니라 **combine 의 generative
property** 에 의존.

## ZFC 와 의 비교 sharper

| Concept | ZFC | 213 |
|---------|-----|-----|
| Set 의 carrier | axiom 으로 commit | type α (임의) |
| 실제 reachable elements | 모든 set element (axiom) | universalMorphism 의 image |
| 둘 의 차이 | 없음 (axiom) | **있음** (Int 가 witness) |

→ 213 framework 가 *carrier vs reach* 의 분리 를 explicit 하게
다룸.  ZFC 는 모든 set element 를 axiom 으로 commit — 분리 부재.

## Axiom 검증

`#print axioms`:
- `int_image_nonneg`: [propext]
- `int_image_strict`: [propext]

Lean 4 core baseline.

## 변경 이력

- 2026-04-25: Int instance 추가.  4번째 catalogue case (infinite
  non-surj) — reach dichotomy 의 complete demonstration.
