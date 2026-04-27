# F0 — 213-native arithmetic synthesis (insights + usage)

## Session journey summary (2026-04-26)

D3 (Real213 = native ℝ) → E1 (full marathon roadmap) → A1-A5 ✓ →
B walls (E2-E4) → E5 (User directive: "213 must stay 213") →
F1 (cutSum working).

## Key insights

### 1. orderProj-Cauchy is primitive

Existing HasModulus's ∀ (m, k), ∃ N, ∀ i, j ≥ N, orderProj match
= Real213's native Cauchy form.  This is 213's counterpart of the
Dedekind cut.

ε-N (Bishop) is a *different abstraction* — within 213 the two forms
are *non-equivalent* (E4: they differ at rational points).  213 uses
native only.

### 2. Arithmetic is at cut-level (RealCut), not sequence-level

Sequence-level lift (Raw realization from E2, multi-precision query
from E3, Cauchy form conflict from E4) — all are side effects of
*importing Bishop's framework*.

**Cut-level**: direct operation on `RealCut := Nat → Nat → Bool`.

```
cutSum(cx, cy, m, k) := ∃ m1 ≤ 2m with cx(m1, 2k) ∧ cy(2m-m1, 2k)
```

5 lines of code, 0 axioms, verified with `decide`.

### 3. The ε/2 trick is an *implementation detail*

The "2k" inside cutSum is Bishop's ε/2 trick — but *user exposure is
unnecessary*.  Wrapped as bounded search, the primitive is
cut-decision.

### 4. Working evidence of "213 stays 213"

Working code from the user directive:

| Operation | Sequence-level attempt | cut-level (F1) |
|-----------|------------------------|----------------|
| Effort | multi-file engineering | ~5 lines |
| Walls | 3 (E2, E3, E4) | none |
| Verification | hard (Cauchy bookkeeping) | `decide` |

= actual demonstration of "it will actually be easier".

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
