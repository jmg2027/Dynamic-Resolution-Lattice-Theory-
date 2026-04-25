# 73 — monotonic propagation: constructive Cauchy fragment

`Research/MonotonicBoundedCauchy.lean` 형식화 + Euler / Wallis
monotonicity instance.

## 목표 (Risk 2 의 본질 분석)

§7 demonstration suite 의 specific cuts (e: m/k ≥ 3, m/k ≤ 2;
π/2: m/k ≥ 2, m/k ≤ 1) 를 **임의 (m, k) cut** 으로 일반화 시도.

## 핵심 결과

### Constructive helpers ([propext, Quot.sound] only)

- `IsAbMonotonic`, `IsAbPositiveB` — ab-sequence 의 monotonic
  / positive-denominator 성질.
- `ab_monotonic_chain` — transitive monotonic: ∀ p ≤ q,
  `a_p * b_q ≤ a_q * b_p`.
- `orderProj_false_propagates` — N 시점 false 는 모든 i ≥ N 에서
  false 로 전파.
- `orderCauchy_from_false_witness` — N₀ false 위트니스 → Cauchy
  at (m, k).
- `orderCauchy_from_true_forever` — ∀ n true → Cauchy at (m, k).

Euler / Wallis instance:
- `euler_isAbMonotonic`, `euler_isAbPositiveB`.
- `wallis_isAbMonotonic`, `wallis_isAbPositiveB`.

### Drop: 일반 `∀ (m, k), ∃ N, …` (LEM 필요)

`monotonic + bounded → isOrderCauchy` (모든 m, k closure) 는
LEM 필요:
- "∀ n, true" vs "∃ n, false" case split 이 `Decidable
  (∀ n : Nat, P n)` 미 보장.
- `push_neg` Mathlib only.
- Constructive 으로 N 을 produce 하려면 sequence-specific
  convergence rate 정보 필요 (e.g., (m, k) 가 limit 에 가까운
  경우 어떤 step 까지 가야 cross 하는지).

## 깊은 framing — 약점 이 아니라 design choice

**213 framework 안에서 표현 가능 한 것 = constructive Cauchy
real (각 cut 의 explicit witness)**.  ZFC 의 set-theoretic ℝ
("임의 Dedekind cut") 와 strict subset 관계.

- ZFC P(ℚ): 임의 부분집합 commitment (LEM 가정 자동).
- 213 의 RealCut: 각 (m, k) 에 explicit Bool witness.

이 관계 는 Risk 1 (Power set) 과 동일 패턴 — note 74 참조.
약점 이 아니라 "213 은 constructive subset 만 다룸" 이라는
design choice.  LEM 자동 commitment 부재 = falsifiability
contract 의 직접 귀결.

## Axiom 검증

`#print axioms`:
- `ab_monotonic_chain`: [propext, Quot.sound]
- `orderProj_false_propagates`: [propext, Quot.sound]
- `orderCauchy_from_false_witness`: [propext, Quot.sound]
- `orderCauchy_from_true_forever`: no axioms (pure constructive)
- `euler_isAbMonotonic`, `euler_isAbPositiveB`: [propext, Quot.sound]
- `wallis_isAbMonotonic`, `wallis_isAbPositiveB`: [propext, Quot.sound]

Classical.choice 부재.  AXIOM §5.2.1 falsifiability 유지.

## Paper 1 §7 closure

전체 (m, k) 자동 closure 대신:
- 각 demonstration (Euler, Wallis) 에 specific cuts 가 explicit
  Bool decision.
- Monotonicity 가 framework-side abstraction 으로 noted.
- General closure 의 LEM 필요 가 명시 적 으로 acknowledged
  (note 74 의 Power set framing 과 통합).

## 변경 이력

- 2026-04-25: MonotonicBoundedCauchy.lean 작성.  General
  isOrderCauchy 가 LEM 필요 임 발견 후 constructive helpers
  로 refactor.  Risk 2 의 본질 (constructive vs ZFC 의 임의성)
  명시.
