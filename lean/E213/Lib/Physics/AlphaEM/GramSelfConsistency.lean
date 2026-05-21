import E213.Lib.Physics.AlphaEM.GradedFormulaPrecision

/-!
# Gram Self-Consistency (C1 Step 3)

Step 3 of conjecture C1 (Pure Cup-Ring α_em) per
`research-notes/G35_chiral_cup_ring_catalog.md` §C1.

Step 1 (`GradedFormula.lean`) established the 5-layer
graded sum at 9-digit precision.

Step 2 (`GradedFormulaPrecision.lean`) showed the residual
stabilises at **2,157 × 10⁻⁹** in 1/α_em (= 2.16 ppm) at
infinite π precision.  Higher π does NOT close it.

Step 3 (this file): identify the residual as the
**α_em² / d² Gram self-energy term** (`Augmented.lean`).
Self-consistency: subtracting it brings precision to ≈ 0.2 ppb.

STRICT ∅-AXIOM (rational decide on big Nat).
-/

namespace E213.Lib.Physics.AlphaEM.GramSelfConsistency

open E213.Lib.Physics.AlphaEM.GradedFormulaPrecision

/-! ## §1 — Gram correction (α²/d²) at 10⁻⁹ + refined formula -/

/-- Squared 1/α_em(observed) × 10¹⁸. -/
def observed_e9_squared : Nat := observed_e9 * observed_e9

/-- Gram self-energy correction at 10⁻⁹:
    α²/d² · 10⁹ = 10²⁷ / (25 · (1/α)²·10¹⁸). -/
def gram_correction_e9 : Nat :=
  1000000000000000000000000000 / (25 * observed_e9_squared)

/-- Refined 1/α_em × 10⁹: π⁵ form minus Gram self-energy. -/
def alphaInv_refined_e9 : Nat :=
  alphaInv_213_e9 - gram_correction_e9

/-! ## §2 — Master C1 Step 3 -/

/-- ★★★★★ Gram Self-Consistency Master (C1 Step 3).
    STRICT ∅-AXIOM.

    Subtracting the α²/d² Gram self-energy correction from
    the π⁵ form (12-digit precision):

      raw      = 137,036,001,241  (residual 2,157 = 2.16 ppm)
      Gram     =          −2,130  (= 10²⁷ / (25·observed²))
      refined  = 137,035,999,111
      observed = 137,035,999,084
      diff     =            +27   (≈ 0.2 ppb, ≈ 70× tighter)

    **Caveat**: the Gram correction uses observed α on its
    RHS (self-referential bootstrap), so this is a consistency
    check, NOT an ∅-axiom derivation.  It DOES establish that
    the 2.16 ppm residual has the right form (α²/d²) and right
    size (2130 vs 2157 actual, 1.2% accuracy).

    Step 4+ (cohomological derivation of d² = NS²·NT prefactor)
    remains open.

    Bundles: observed² value, Gram correction value (2130),
    closeness to actual residual (+27 = 2157), refined formula
    value, refined residual (+27), refined bracket (±30), raw
    and refined residual sizes, improvement factor (≥ 71). -/
theorem gram_self_consistency_master :
    -- observed² × 10¹⁸
    observed_e9_squared = 18778865044950048839056
    -- Gram correction value
    ∧ gram_correction_e9 = 2130
    -- Gram + 27 = full 2157 residual
    ∧ gram_correction_e9 + 27 = 2157
    -- Refined formula value
    ∧ alphaInv_refined_e9 = 137035999111
    -- Refined residual = +27
    ∧ alphaInv_refined_e9 = observed_e9 + 27
    -- Refined bracket: |refined − observed| ≤ 30
    ∧ alphaInv_refined_e9 ≤ observed_e9 + 30
    ∧ observed_e9 ≤ alphaInv_refined_e9 + 30
    -- Raw vs refined residual sizes
    ∧ alphaInv_213_e9 - observed_e9 = 2157
    ∧ alphaInv_refined_e9 - observed_e9 = 27
    -- Improvement factor (raw / refined ≥ 71)
    ∧ 2157 / 30 ≥ 71 := by decide

end E213.Lib.Physics.AlphaEM.GramSelfConsistency
