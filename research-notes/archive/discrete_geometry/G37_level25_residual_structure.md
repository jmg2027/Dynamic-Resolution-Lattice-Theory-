# G37 — Level-25 Residual Structure

**Date**: 2026-05-08 (post G36)
**Origin**: Mingu's question — what survives at the CD ceiling?

## The peeling sequence

CD tower bleeds out properties:
- 0→1: ordering lost
- 1→2: commutativity lost
- 2→3: associativity lost
- 3→4: alternativity lost
- 4→5+: power-associativity lost
- ... → 25: d=5 substrate exhausted

## The answer

At level 25 = N_U, **Z/2-graded substrate-valued algebra**:

  1. **Conjugation involution** `cdConj` — recursive
     `(a,b)̄ = (ā, b)`, involutive at every level.
  2. **Substrate-valued norm** `cdNormSq : CDLevel n → Cut`
     via recursive cutSum/cutMul.
  3. **Z/2 grading** by conjugation eigenspaces.
  4. **N_U cardinality** = 5²⁵ trajectory branches.

This is **not** a normed division algebra (lost before level 4),
**not** a Lie algebra (lost at level 3), but IS involutive +
substrate-valued + finitely cardinalised.

## Connection to physics

Level-25 residual structure IS the operational substrate of
DRLT physics:
  * Conjugation `cdConj` = charge conjugation symmetry
  * Norm `cdNormSq` = amplitude squared (probability density)
  * N_U = 5²⁵ = universe finite cardinality

Not coincidence: physics emerges from the residual structure
that survives the CD tower's saturation on d=5 substrate.

## Formalization

  * `Lib/Math/SignedCut/CDConjugation.lean` — recursive `cdConj`,
    `cdConj_involutive` at every level.
  * `Lib/Math/SignedCut/CDNorm.lean` — substrate-valued
    `cdNormSq`.
  * `Lib/Math/SignedCut/Level25Residual.lean` — explicit
    level-25 witnesses.
  * `Lib/Math/SignedCut/Level25Capstone.lean` — 5 cluster
    witnesses incl. total_witness.

All ∅-axiom; closed-form `5^25 = 298023223876953125` checked
at the Lean kernel.

## Filed under

  * G36 (CD basis unification, PR #62)
  * G36-followup (Mul rule + Hurwitz, PR #63)
  * `seed/RESOLUTION_LIMIT_SPEC.md` (N_U system invariant)
