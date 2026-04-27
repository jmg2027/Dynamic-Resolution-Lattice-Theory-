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

### Pattern for defining new operations

For unary op f (e.g., negation, abs, ...):
1. Define: `cutF (cx) (m, k) := bounded predicate on cx`.
2. Verify: `decide` matches expected on rational instances.

For binary op ⊕ (add, mul, ...):
1. Define: `cut⊕ (cx, cy) (m, k) := bounded search over decompositions`.
2. Verify: `decide` on rational instances.
3. (Optional) Lift: Real213 → RealCut via OrderCauchyData.toRealCut.

### No sequence-level bypass

Real213's sequence (xs, modulus) itself is *internal implementation*.
External API is RealCut only.  Raw constructors for sequences (Pell,
etc.) are *witnesses* only — no primitive arithmetic.

This is the *meaning* of 213-native: cuts are primitive, sequences are
witnesses.

### Lifting RealCut → Real213 (open)

Does every RealCut have a Real213 origin?  → Does every *valid* cut
belong to some Real213?

- Every cut of OrderCauchyData has a Real213 origin (by definition).
- Not every Nat → Nat → Bool is valid — must satisfy monotonicity,
  locatedness, and other properties.

*Valid* RealCut = monotone + dense + ... — full characterization is
separate work.

## Next arc (F2-F5 + Phase C onward)

| # | Milestone | Approach |
|---|-----------|----------|
| F2 | cutMul (multiplication) | bounded search on (m1, k1, m2, k2) |
| F3 | cutNeg / signed Real213 | extend Real213 with sign bit or swap-Lens |
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
