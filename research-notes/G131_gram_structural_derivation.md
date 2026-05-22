# G131 — Gram self-energy structural derivation

**Date**: 2026-05-22
**Status**: ANCHOR (Phase 1 of structural-close marathon)
**Branch**: `claude/g121-open-followup-BCOp3`
**Source**: post-merge HANDOFF, identified as "principal
physics-layer open problem" from n-u-followup branch
(out of N_U-family scope).

## Why this is the next valuable open frontier

The n-u-followup branch's HANDOFF explicitly flagged this as the
**principal physics-layer open problem**:

> Structural derivation of the Gram self-energy term in
> `AlphaEM/Augmented.lean:134-141` (the 4 ppm structural gap of
> `1/α_em`).  Out of scope for N_U-family work; logged as the
> principal physics-layer open problem.

Closing this gap promotes `1/α_em` from "near-precision-theorem"
(0.07 ppm via existing AlphaEM infrastructure) to "precision-
theorem at the structural-derivation tier" — a direct path to
DRLT Validation Standard satisfaction per
`seed/AXIOM/08_falsifiability.md`.

## Current state (pre-G131)

`GramSelfConsistency.lean` proves that subtracting the Gram
correction `α²/d²` from the 5-layer base formula brings the
residual from 2,157 × 10⁻⁹ (= 2.16 ppm) to 27 × 10⁻⁹ (= 0.2 ppb,
~70× tighter).

But the Gram correction is computed self-referentially from
observed α (`gram_correction_e9 := 10²⁷ / (25 · observed²)`),
NOT derived from 213-atomic principles.  This is a self-
consistency check, not a precision theorem.

## The G131 framework (anchor laid 2026-05-22)

`lean/E213/Lib/Physics/AlphaEM/GramStructural.lean` (11 PURE):

### Key insight: the cubic self-consistency identity

The Augmented.lean docstring mentions a self-consistency
polynomial.  The **corrected form** (sign-fix from "+1" to "+1"
on the LHS, not RHS):

  **25·y³ + 1 = 25·X·y²**

where `y = 1/α_em` and `X = alphaInv_213_e9 / 10⁹` (5-layer base).

Rearranges to:

  **X − y = 1 / (25 · y²) = α² / d²**     (with d² = 25)

The Gram correction `α²/d²` is **structurally forced** as the
cubic-root deviation `X − y`, NOT an arbitrary numerical input.

### Anchor file contents

  · `cubic_lhs_25y3`, `cubic_rhs_25Xy2`, `cubic_one_e27` —
    cubic terms at e27 scale (Nat-safe)
  · `cubic_residual_e27` — Nat-valued residual measuring deviation
    from exact cubic satisfaction
  · `gap_e9 = 2157` — 5-term-vs-observed gap
  · `gram_correction_value`: `gram_correction_e9 = 2130` (matches
    GramSelfConsistency)
  · `post_gram_residual_eq_27`: `gap_e9 − gram = 27` (next-order
    target)
  · ★★★★ `gram_structural_bracket` (6-conjunct capstone): full
    bracket decomposition + percentages (Gram captures 98.7% of
    gap; post-Gram residual < 1/70 of original)

### Numerical decomposition (at e9 scale)

```
alphaInv_213_e9 (= X·10⁹)      = 137,036,001,241
observed_e9    (= y·10⁹)       = 137,035,999,084
                                ─────────────────
gap_e9 (X − y at e9)          =          2,157  (2.16 ppm)
gram_correction_e9            =          2,130  (2.13 ppm)
                                ─────────────────
post_gram_residual_e9         =             27  (0.2 ppb)
```

The Gram correction `2,130` is 98.7% of the gap `2,157`.

## Open work for full structural close (G131 Phase 2+)

### Phase 2 — Cubic uniqueness + bracket

Prove the cubic `25·y³ + 1 = 25·X·y²` has a unique real root
y(X) in a small bracket around X for any X in the physics
range (X ≈ 137).  Use rational discriminant analysis.

### Phase 3 — Newton iteration for cubic root

Replace `gram_correction_e9` definition with a Newton-on-the-cubic
iteration:
  · Start from y₀ = X
  · Iterate y_{n+1} = y_n − (25·y_n³ + 1 − 25·X·y_n²) / (75·y_n² − 50·X·y_n)
  · Converge to y satisfying the cubic at desired precision

This yields a **213-internal** value for the Gram correction,
removing the self-referential observed-α dependency.

### Phase 4 — Post-Gram residual (27 × 10⁻⁹) decomposition

The 27 × 10⁻⁹ residual after subtracting the Gram correction is
the next-order target.  Candidates per `StructuralGap.lean`:
  · (α_GUT/4)² Dyson tail ≈ 3.7 × 10⁻⁵ — too small by ×15
  · Refined d²/NS coefficient 25/3·(1 + δ), δ ≈ 6.5 × 10⁻⁵
  · Hadronic-sector 213-internal analog

Resolving this 27 × 10⁻⁹ is the **second-tier** structural target.

### Phase 5 — Precision theorem promotion

Once Phase 2-4 close, `1/α_em` becomes a fully 213-internal
precision theorem at the 27 × 10⁻⁹ ≈ 0.2 ppb level — satisfying
DRLT Validation Standard.

## Estimated scope

| Phase | Content | PURE est. | Sessions est. |
|---|---|---|---|
| 1 | Anchor (THIS) | 11 (done) | 1 (done) |
| 2 | Cubic uniqueness + bracket | ~40 | 2-3 |
| 3 | Newton cubic-root iteration | ~50 | 3-4 |
| 4 | Post-Gram 27 × 10⁻⁹ resolution | ~60 | 3-5 |
| 5 | Precision-theorem capstone | ~20 | 1-2 |

**Total to full close**: ~180 PURE, 10-15 sessions.

## Connection to existing infrastructure

  · `Lib/Physics/AlphaEM/GradedFormulaPrecision.lean` — X at e9
  · `Lib/Physics/AlphaEM/GramSelfConsistency.lean` — observed-based
    Gram correction
  · `Lib/Physics/AlphaEM/Augmented.lean` — `α²/d² ≈ 213/10⁸`
    framing + bracket containment of CODATA
  · `Lib/Physics/AlphaEM/StructuralGap.lean` — gap statement + 3
    candidate-correction classes

## Falsifier potential

**HIGH** — `1/α_em` is the most precisely measured fundamental
constant.  Promoting the 213 derivation from "self-consistency
check" to "structural precision theorem" makes it a falsifier
candidate: if the cubic-root y(X) disagrees with future CODATA
measurements beyond the structural error bound, the 213 framework
is falsified.
