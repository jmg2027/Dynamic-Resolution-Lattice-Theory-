# G63: Orthogonal-axis tower synthesis — k-axis ℕ^k → ℤ^{k-1}

## Status

**Synthesis** of G62 (2-axis) + tentative 3-axis exploration.
Both Lean ∅-axiom closures complete.

## The framework

Following user's reframing of ℕ→ℤ as **two orthogonal axes +
diagonal quotient projection**, the natural generalization is:

> **L_k = ℕ^k / diagonal-translation ≅ ℤ^{k-1}**

Each layer adds one orthogonal ℕ-axis; the diagonal quotient
collapses the redundant common-shift dimension.

| k | ℕ^k | quotient | result | Lean file |
|---|---|---|---|---|
| 1 | ℕ | identity | ℕ | (trivial) |
| 2 | ℕ² | (a+t, b+t) ~ (a, b) | ℤ | `NatPairToInt.lean` |
| 3 | ℕ³ | (a+t, b+t, c+t) ~ (a, b, c) | ℤ² | `NatTripleToZ2.lean` |
| 4 | ℕ⁴ | diag-shift | ℤ³ | (not yet) |
| 5 | ℕ⁵ | diag-shift | ℤ⁴ | (= 213-universe?) |

So orthogonal-axis tower **strictly grows by 1 dimension per step**
(after the first quotient).

## Eisenstein discovery (3-axis case)

The 3-axis projection `(a, b, c) ↦ (a-c, b-c)` makes the three
unit axes map to:

| ℕ³ axis | ℤ² image | Eisenstein |
|---|---|---|
| (1, 0, 0) | (1, 0) | 1 |
| (0, 1, 0) | (0, 1) | ω |
| (0, 0, 1) | (-1, -1) | ω² |

**Sum = (0, 0)** — exactly the relation `1 + ω + ω² = 0`.

So the 3-axis L_3 ≅ ℤ² **carries the Eisenstein structure for
free**: the three ℕ-axes realize the three cube-roots of unity.

Lean ∅-axiom witness: `three_axes_sum_to_zero`.

## Implication: 4-row matrix natural embedding?

If "k-axis ℕ^k" gives a tower where each layer carries some
natural cyclotomic structure:

- L₂ = ℤ (Z₂ = {±1} embedded — 2-fold cyclotomic)
- L₃ = ℤ² (Z₃ = {1, ω, ω²} embedded — 3-fold cyclotomic)
- L₄ = ℤ³? (Z₄ = ZI-like? or something else)
- L₅ = ℤ⁴? (Z₅ = ζ_5 = where φ lives algebraically?)

The k-fold cyclotomic embedding is natural because:
- ℕ^k has S_k symmetric group action (axis permutation)
- After diagonal quotient, the residual S_k action is on ℤ^{k-1}
- Cyclic Z_k ⊂ S_k acts as cyclic shift on the k axes
- This gives a Z_k-action on ℤ^{k-1} → matches cyclotomic structure

| k | Z_k action on ℤ^{k-1} | matches |
|---|---|---|
| 2 | ±1 on ℤ | ZI? no, ZI is Z_4.  Actually just sign-flip |
| 3 | rotation by ω on ℤ² | Eisenstein ZOmega |
| 4 | rotation by i on ℤ³? | check |
| 5 | rotation by ζ_5 on ℤ⁴? | check |

This is conjectural; needs exploration.

## What doesn't fit

The 4-row matrix has:
- Type A: ZI = ℤ[i] (Z_4 / Z_2-extension of ℤ)
- Type B: ZSqrt[-D] (Z_2 only)
- Type C: ZOmega = ℤ[ω] (Z_6 = Z_2 × Z_3)
- Type D: Hurwitz (Z_24 = 2T binary tetrahedral)

Under orthogonal-axis tower:
- L_3 = ℤ² with Z_3 → matches **Type C** (Eisenstein)
- L_2 = ℤ with Z_2 → matches **Type B** (most basic)
- Type A (ZI) and Type D (Hurwitz) **don't directly fit** the
  orthogonal-axis chain — they need different quotients or
  different axis configurations

Possible interpretation: the 4-row matrix is NOT a single tower
but **4 distinct doubling paths**, each starting from a different
quotient at L_2.

## Remaining questions

1. Does 4-axis ℕ⁴ → ℤ³ give Z_4 = i-rotation = ZI?  Probably NOT
   (ZI is 2D, but ℤ³ is 3D).  Suggests ZI requires DIFFERENT
   quotient (not pure diagonal).

2. Where do Type A and Type D fit?  Likely different quotients
   on ℕ^4 / ℕ^∞.  Hurwitz quaternion = 4D non-commutative.

3. What's the 213-meaning of L_5 = ℤ⁴?  d=5 universe...

4. Is the cyclotomic conjecture (L_k carries Z_k) provable as
   ∅-axiom for general k?

## Lean ∅-axiom inventory (this synthesis)

| Theorem | File | Status |
|---|---|---|
| npairEquiv_refl/symm | NatPairToInt | ∅ |
| npairToInt_natToNPair | NatPairToInt | ∅ |
| npairToInt_natToNPairNeg | NatPairToInt | ∅ |
| npairToInt_zero | NatPairToInt | ∅ |
| npairToInt_diag_shift | NatPairToInt | ∅ |
| npairToInt_translation_invariant | NatPairToInt | ∅ |
| zero_fiber_multiple | NatPairToInt | ∅ |
| negative_axis_witness | NatPairToInt | ∅ |
| swap_realizes_negation | NatPairToInt | ∅ |
| ntripleToZ2_origin | NatTripleToZ2 | ∅ |
| ntripleToZ2_axis_1/2/3 | NatTripleToZ2 | ∅ |
| three_axes_sum_to_zero | NatTripleToZ2 | ∅ |
| ntripleToZ2_diag_invariant | NatTripleToZ2 | ∅ |

**15 ∅-axiom theorems** for the orthogonal-axis tower foundation.

## See also

- `lean/E213/Theory/Tower/NatPairToInt.lean` — 2-axis closure
- `lean/E213/Theory/Tower/NatTripleToZ2.lean` — 3-axis closure
- `lean/E213/Theory/Raw/Signed.lean` — Raw swap = Int negation
- `research-notes/G61_213_tower_research_candidates.md` — candidate list
- `research-notes/G62_nat_to_int_orthogonal.md` — orthogonal framing + losses
