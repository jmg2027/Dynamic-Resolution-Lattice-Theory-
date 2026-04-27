# F0 — 213-native arithmetic synthesis (insights + usage)

## Session journey 요약 (2026-04-26)

D3 (Real213 = native ℝ) → E1 (full marathon roadmap) → A1-A5 ✓ →
B walls (E2-E4) → E5 (User directive: "213 은 213 해 야 만 해") →
F1 (cutSum working).

## 핵심 통찰

### 1. orderProj-Cauchy 가 primitive

기존 HasModulus 의 ∀ (m, k), ∃ N, ∀ i, j ≥ N, orderProj 일 치
= Real213 의 native Cauchy form.  이 것 이 Dedekind cut 의 213
counterpart.

ε-N (Bishop) 은 *다 른 abstraction* — 213 안 에 서 두 form 이 *non-
equivalent* (E4: rational point 에 서 differ).  213 은 native 만.

### 2. Arithmetic 은 cut-level (RealCut), 아니라 sequence-level

Sequence-level lift (E2 의 Raw realization, E3 의 multi-precision
query, E4 의 Cauchy form 갈등) — 모두 *Bishop framework import*
의 부 작용.

**Cut-level**: `RealCut := Nat → Nat → Bool` 위 에 서 직접 operation.

```
cutSum(cx, cy, m, k) := ∃ m1 ≤ 2m with cx(m1, 2k) ∧ cy(2m-m1, 2k)
```

5 줄 코드, 0 axioms, decide 로 verify.

### 3. ε/2 trick 은 *implementation detail*

cutSum 안 의 "2k" 가 Bishop 의 ε/2 trick — 하 지 만 사용자 노출
*불필요*.  Bounded search 로 wrapped, primitive 는 cut-decision.

### 4. "213 은 213" 의 working evidence

User directive 의 working code:

| Operation | sequence-level 시도 | cut-level (F1) |
|-----------|------|-----|
| Effort | multi-file engineering | ~5 lines |
| Walls | 3 (E2, E3, E4) | none |
| Verification | hard (Cauchy bookkeeping) | `decide` |

= "오 히 려 더 쉬울 거" 의 실제 demonstration.

## Usage method

### 새 operation 정의 패 턴

For unary op f (e.g., negation, abs, ...):
1. 정의: `cutF (cx) (m, k) := bounded predicate on cx`.
2. Verify: rational instances 에 서 `decide` 로 expected match.

For binary op ⊕ (add, mul, ...):
1. 정의: `cut⊕ (cx, cy) (m, k) := bounded search over decompositions`.
2. Verify: rational instances 에 서 `decide` 로.
3. (선 택) Lift: Real213 → RealCut via OrderCauchyData.toRealCut.

### Sequence-level 우 회 부재

Real213 의 sequence (xs, modulus) 자체 는 *internal implementation*.
External API 는 RealCut 만.  Sequence 의 Raw constructor (Pell, etc.)
는 *witness* 로 만 — primitive arithmetic 부재.

이 게 213-native 의 *의 미*: cut 이 primitive, sequence 는 witness.

### Lifting RealCut → Real213 (open)

모든 RealCut 가 Real213 origin 인가?  → 모든 *valid* cut 이 어떤
Real213 의 cut 인가?

- 모든 OrderCauchyData 의 cut 은 Real213 origin (정의 상).
- 모든 Nat → Nat → Bool 이 valid 는 아 님 — monotonicity, locatedness
  등 properties 만족 필 요.

*Valid* RealCut = monotone + dense + ... — full characterization 별 도
작업.

## 다 음 arc (F2-F5 + Phase C onward)

| # | Milestone | Approach |
|---|-----------|----------|
| F2 | cutMul (multiplication) | bounded search on (m1, k1, m2, k2) |
| F3 | cutNeg / signed Real213 | extend Real213 with sign bit 또 는 swap-Lens |
| F4 | RealCut → Real213 lift (partial) | for "valid" cuts |
| F5 | Real213 arithmetic via cut roundtrip | full add/mul/neg/div on Real213 |
| C2-C3 | Cauchy in Real213 + completeness | distance via cutSum + cutNeg |
| D-H | continuity, calculus, IVT | standard Bishop on top |

## Cross-references

- `framework/E213/Research/Real213.lean` — type 정의.
- `framework/E213/Research/Real213{Equiv,Const,Order,Sign,OrderExtra}.lean`
  — Phase A complete.
- `framework/E213/Research/Real213CutSum.lean` — F1 cutSum.
- `framework/E213/Research/Real213CutSumTest.lean` — verifications.
- `notes/D3, E1-E5` — context.
