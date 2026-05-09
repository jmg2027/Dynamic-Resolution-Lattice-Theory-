import E213.Lib.Physics.AlphaEM.GradedFormula

/-!
# Graded Formula Precision (C1 Step 2)

Step 2 of conjecture C1 (Pure Cup-Ring α_em) per
`research-notes/G35_chiral_cup_ring_catalog.md` §C1.

Step 1 (`GradedFormula.lean`) gave the 5-layer formula at
9-digit π precision matching observed 137.0359991 to within
20 × 10⁻⁷ (= 2 ppm).

Step 2 (this file): scale to 12-digit precision (10⁻⁹ units)
and document the residual.

## Honest assessment

At infinite π precision, the 5-layer formula
  60·ζ(2) + 30 + 25/3 + α_GUT/(NS+1) + 1/(NS·NT·π⁵)
evaluates to 137.036001242, **off observed 137.035999084 by
2.16 × 10⁻⁶ = 2.16 ppm**.  Higher precision π does NOT close
this gap — it's a structural offset.

The remaining 2.16 ppm corresponds (in the existing AlphaEM
formulation `Augmented.lean`) to the **α_em²/d² Gram
self-energy term** ≈ 2.13 × 10⁻⁶.  This is currently a
self-referential bootstrap (uses observed α_em).  Closing it
∅-axiom requires either:
  (a) Replacing the π⁵ form with one that captures the Gram
      contribution as well (e.g., a different sub-Wallis form);
  (b) Adding a separate L=2+ fractal-correction layer
      (per `FractalLevelLift.lean`).

For now, the formula is decide-checked to bracket observed
within ~2 ppm at 10⁻⁹ precision.

STRICT ∅-AXIOM (decide on Nat division at high precision).
-/

namespace E213.Lib.Physics.AlphaEM.GradedFormulaPrecision

/-! ## §1 — 12-digit π values -/

/-- π² × 10¹² (12-digit precision).  π² = 9.869604401089... -/
def pi2_e12 : Nat := 9869604401089

/-- π⁵ × 10¹² (12-digit precision).  π⁵ = 306.019684785281... -/
def pi5_e12 : Nat := 306019684785281

/-! ## §2 — Formula at 10⁻⁹ units (12-digit precision) -/

/-- 1/α_em(IR) candidate × 10⁹ via the 5-layer formula at
    12-digit π precision. -/
def alphaInv_213_e9 : Nat :=
  let pi2 := pi2_e12
  let pi5 := pi5_e12
  -- l1a = 60·ζ(2)·10⁹ = 10·π²·10⁹ = π²·10¹⁰ = pi2 / 10²
  let l1a := pi2 / 100
  -- l1b = 30·10⁹
  let l1b := 30 * 1000000000
  -- l2 = (25/3)·10⁹ = 25·10⁹/3
  let l2 := 25 * 1000000000 / 3
  -- l4 = α_GUT/4·10⁹ = 6/(100π²)·10⁹ = 6·10²¹ / (100·pi2)
  let l4 := 6 * 1000000000000000000000 / (100 * pi2)
  -- l3 = 1/(6π⁵)·10⁹ = 10²¹ / (6·pi5)
  let l3 := 1000000000000000000000 / (6 * pi5)
  l1a + l1b + l2 + l4 + l3

theorem alphaInv_213_e9_value :
    alphaInv_213_e9 = 137036001241 := by decide

/-- Observed 1/α_em(0) × 10⁹ = 137,035,999,084 (CODATA 2024). -/
def observed_e9 : Nat := 137035999084

/-- Diff in 10⁻⁹ units: 2157 (= 2.16 × 10⁻⁶ relative ≈ 2.16 ppm).
    This residual is the structural Gram self-energy α_em²/d²
    NOT captured by the π⁵ form. -/
theorem alphaInv_213_residual :
    alphaInv_213_e9 = observed_e9 + 2157 := by decide

/-- Bracket: |formula − observed| ≤ 2200 in 10⁻⁹ units. -/
theorem alphaInv_213_bracket_e9 :
    alphaInv_213_e9 ≤ observed_e9 + 2200
    ∧ observed_e9 ≤ alphaInv_213_e9 + 2200 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §3 — Master C1 Step 2 theorem -/

/-- ★★★★★ Graded Formula Precision Master (C1 Step 2).
    STRICT ∅-AXIOM.

    At 12-digit π precision (10⁻⁹ units):
      formula = 137,036,001,241
      observed = 137,035,999,084
      residual = 2,157 (= 2.16 ppm)

    This 2.16 ppm residual corresponds to the α_em²/d² Gram
    self-energy term (≈ 2.13 ppm).  Without that term (or its
    cohomology-derived replacement), the π⁵ form alone is off
    observed by 2.16 ppm.  Higher π precision does NOT close
    this gap — it's a structural offset.

    Fully closing C1 requires either Gram-replacement at the
    cohomology level (e.g., L=2+ fractal correction) or a
    different Wallis-bracket combination.  This file documents
    the residual at the current precision. -/
theorem graded_formula_precision_master :
    alphaInv_213_e9 = 137036001241
    ∧ observed_e9 = 137035999084
    ∧ alphaInv_213_e9 = observed_e9 + 2157
    ∧ alphaInv_213_e9 ≤ observed_e9 + 2200
    ∧ observed_e9 ≤ alphaInv_213_e9 + 2200 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.AlphaEM.GradedFormulaPrecision
