# E3 — ModulusCombiner kernel 의 깊은 obstruction

## Kernel 의 구축 (2026-04-26)

`Real213ModulusCombiner.lean`: abstract kernel 완성.

```
structure ModulusCombiner (combine : Raw → Raw → Raw) where
  precX : Nat → Nat → Nat × Nat
  precY : Nat → Nat → Nat × Nat
  precX_k_pos / precY_k_pos
  preserves : ... — orderProj 일 치 propagation
```

`combineModulus` generic theorem: 두 HasModulus + ModulusCombiner →
combined HasModulus.  Cauchy bookkeeping 이 *one place* 격리 ([propext]
only).

## Trivial instances ✓ (kernel 검증)

- `piOneCombiner` : combine x y = x (0 axioms).
- `piTwoCombiner` : combine x y = y (0 axioms).
- `constCombiner c` : combine = constant c (0 axioms).

위 3 instance 가 kernel 의 well-formedness 확인.

## Addition 의 deeper obstruction

Addition combiner 시도 시 *근본 적* 문제 발견:

**Single-precision query 의 information 부족**.

ModulusCombiner 의 preserves: x1, x2 가 *single* precision (m_x, k_x)
에 서 orderProj 일 치, y1, y2 가 *single* precision (m_y, k_y) 에 서
orderProj 일 치 → combined 가 (m, k) 에 서 일 치.

Addition: orderProj of sum view (a*b' + a'*b, b*b') at (m, k) =
decide ((a*b' + a'*b)*k ≤ b*b'*m).  이 결정 은 (a, b, a', b') 의
*exact value* 에 의존 — single precision 에 서 의 cut decision 만
으 로 는 결정 부재.

**Counterexample**: x1 view (1, 2), x2 view (2, 4) — 둘 다 ratio 1/2.
orderProj 1 2 of (1, 2) = decide(2 ≤ 2) = true.  orderProj 1 2 of
(2, 4) = decide(4 ≤ 4) = true.  Single precision 일 치.

But sum with y view (1, 1): sum1 view = (1*1 + 1*2, 2*1) = (3, 2),
sum2 view = (2*1 + 1*4, 4*1) = (6, 4).  Ratios 모두 3/2 — orderProj
일 치 OK at any (m, k).  다행히 같음.

Hmm — *이 specific case* 는 ratio 가 같으 니 OK.  하 지 만 일반 적
으 로 view 의 *value* 가 다 르 면 orderProj 의 일 치 가 view-equality
가 아 니 라 *cut-side* equality 만 보 장.

## 진 짜 issue

Cauchy sequence 의 view 가 *value* 로 stabilize 안 함 — orderProj
*decision* 만 stabilize.  Addition 의 sum view 의 orderProj 는 view
의 *value-pair* 에 의존.  Decision-side 만 으 로 는 sum decision 결정
부재.

## 가능 한 해결 방향

### (A) Multiple-precision queries

ModulusCombiner 를 확장: precX 가 single precision 이 아 닌 *list*
of precisions.  Bishop 의 ε/2 trick 의 213 form — 여 러 cut decision
조합 으 로 sum decision 좁 히 기.

```
structure ModulusCombiner (combine) where
  precX : Nat → Nat → List (Nat × Nat)
  preserves : ... ∀ p ∈ precX, orderProj p of x1 = of x2 → ...
```

이 design 이 더 expressive.  하 지 만 *얼마 나 많은 precision* 이
필 요 한 가 가 case-specific.

### (B) Stronger Cauchy form — bounded view variation

HasModulus 를 확장: orderProj 의 stability 뿐 아 니 라 view-value
의 *bounded variation* 도 보 장.

```
structure StrongModulus where
  N : Nat → Nat → Nat
  cauchy_at : ...  -- orderProj
  view_bound : ∀ ε > 0, ∃ N, ∀ i j ≥ N, |view i - view j| < ε
```

이 형식 으 로 는 addition 이 자연 — Bishop 의 standard.  하 지 만
*기존* HasModulus 와 의 호환 부재 — Pell, Diagonal 등 의 instance
re-prove 필 요.

### (C) Cut-level addition

`RealCut := Nat → Nat → Bool` 위 에 서 직접 addition 정의.  단,
∃-quantifier-heavy.  Decidability 부재.

## 결정

**(B) 권 장** — Bishop 의 ε-N standard 와 정 합, 외 부 axiom 부재.
HasModulus 를 *strict* form 으 로 강화 + 기존 instance 들 재증명.
이 게 진 짜 long arc.

또 는 (A): 더 abstract, 하 지 만 case-specific tuning 필 요.

## Falsifiability

이 obstruction 도 *engineering challenge* — Bishop 의 program 자체
가 working (외부 mathematics literature), 단순 213 안 *바 른 abstraction
선택* 의 문제.

## 다 음

- **F1 (proposed)**: `StrongModulus` typeclass + 기존 instance (Pell,
  Diagonal) 의 재증명.
- **F2 (proposed)**: `StrongModulus` 위 의 ModulusCombiner kernel.
- **F3 (proposed)**: Addition 의 instance.

별 도 큰 arc — 이 session 에 서 는 *진단* 까 지 만.
