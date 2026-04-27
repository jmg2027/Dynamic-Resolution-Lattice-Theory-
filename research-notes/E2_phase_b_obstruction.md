# E2 — Phase B (Arithmetic) 의 Raw-realization obstruction

## 발 견 (2026-04-26)

Phase B1 (Real213 addition) 시도 중 다음 obstruction 발 견.

## abLens.view 의 image

`framework/E213/Research/PellSeq.lean` 의 `abLens_surjective`:

```
∀ a b : Nat, a + b = s → 1 ≤ a → 1 ≤ b → ∃ r : Raw, abLens.view r = (a, b)
```

**Image 의 정확한 description**:

```
range(abLens.view) = {(1, 0)} ∪ {(0, 1)} ∪ {(a, b) : a ≥ 1 ∧ b ≥ 1}
```

증거:
- (1, 0): Raw.a 의 view.
- (0, 1): Raw.b 의 view.
- (a, b), a ≥ 1, b ≥ 1: abLens_surjective.
- (0, k) for k ≥ 2: **realizable Raw 부재** — slash 가 distinct 요구
  → b-leaves 만 으 로 조립 불가.
- (k, 0) for k ≥ 2: 같은 이유 로 부재.

## Addition obstruction

a/b + a'/b' 의 view = (a*b' + a'*b, b*b').

핵심 obstruction case: 두 sequence 가 동시에 "0-counts" 누적,
sum view 의 b-count ≥ 2 가 발생.  예: (0, 1) seq + (a, b≥1 with a=0)
seq → boundary 부재.

## 진 짜 issue

Raw 의 view image 가 *정 확 한* 형식 으 로 제한.  Real213 의
sequence 는 Raw 만 으 로 만들 어 지 므 로 view 가 image 안.  하 지 만
*sum 의 view 도* image 안 이 어 야 Real213 으 로 lift 가능.

Sum image 가 *항상* range 안 으 로 closed 인 가? — **No.**
(1, 0) + (1, 0) = (0, 0) 이 boundary case (Raw.a + Raw.a, "infinity +
infinity").

## 해 결 책 후보

### (i) Real213StrictPos: 모든 view 가 (a, b) with a, b ≥ 1

```
structure Real213StrictPos extends Real213 where
  view_pos : ∀ i, (abLens.view (xs i)).1 ≥ 1 ∧
                  (abLens.view (xs i)).2 ≥ 1
```

이 subtype 위 에 서 는 addition 이 well-defined:
- (a, b), (a', b') with a, b, a', b' ≥ 1 → sum view = (a*b' + a'*b,
  b*b') with both ≥ 1, abLens_surjective 가능.

### (ii) Equivalence-class addition (defer)

Real213 을 equiv-class 로 보 고, 임의 r 의 *대 표* 를 strict
positive view 로 선택.  더 abstract.

## 결정

**(i) 채택 권 장** — most concrete, framework-internal, axiom 추가
부재.  Phase B 작업 은 `Real213StrictPos` 위 에 서 진행, 추 후
`Real213StrictPos → Real213` 의 cut-equivalence 와 의 호환 별 도
작업.

## Falsifiability 의 의미

이 obstruction 이 *framework boundary* 인 가?

- **NO**: addition 자체 는 framework 안 가능 — 단, *type 의
  refinement* 필 요 (StrictPos).  Workaround 존재.
- *Hidden axiom 추가 부재* — 모든 작업 framework-internal.

따라서 falsifiability trigger 아 님 — 단순 *engineering challenge*
(type refinement).

## E1 roadmap 갱신

- Phase B 의 모든 milestone 이 `Real213StrictPos` 위 에 서 의 작업.
- Phase A 추가:
  - A6 (proposed): `Real213StrictPos` subtype 정의 + Real213 ↔
    StrictPos 의 cut-equivalence 호환.

## Next

E2 의 결정 채택 후, `Real213StrictPos.lean` + `Real213Add.lean` 작업.
