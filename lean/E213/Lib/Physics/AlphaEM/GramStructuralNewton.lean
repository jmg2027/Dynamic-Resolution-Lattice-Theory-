import E213.Lib.Physics.AlphaEM.GramStructuralBracket

/-!
# Gram structural derivation — Phase 3: Newton-from-X structural Gram

Phase 1 established the cubic identity `25y³ + 1 = 25Xy²`.
Phase 2 located the cubic root in `(X − 2131, X − 2129)`.

Phase 3 (this file) replaces the self-referential observed-α-in-RHS
computation of `gram_correction_e9` with a **Newton iteration**
starting from `y₀ = X` on the cubic `f(y) = 25y³ + 10²⁷ − 25Xy²`:

  f(y)  = 25y³ + 10²⁷ − 25Xy²
  f'(y) = 75y² − 50Xy

At `y₀ = X`:
  f(X)  = 10²⁷
  f'(X) = 25X²

Newton step: `y₁ = X − f(X) / f'(X) = X − 10²⁷ / (25X²)`.

The correction `X − y₁ = 10²⁷ / (25X²)` is the **structural Gram
correction** — no observed α in the RHS, only the 213-internal
5-layer base X.

**Headline result**: at Newton-1 precision, the structural and
observed-based Gram corrections agree **exactly** at e9 scale
(both = 2130).  Difference between observed and X is small enough
(2,157 × 10⁻⁹ on a value of ~137 × 10⁹ = ~1.6 × 10⁻⁸) that
`X² ≈ observed²` to better than e9-rounding precision.

This closes the self-referentiality of `gram_correction_e9` at
Newton-1 precision.
-/

namespace E213.Lib.Physics.AlphaEM.GramStructuralNewton

open E213.Lib.Physics.AlphaEM.GramStructural (cubic_one_e27)
open E213.Lib.Physics.AlphaEM.GradedFormulaPrecision (alphaInv_213_e9 observed_e9)
open E213.Lib.Physics.AlphaEM.GramSelfConsistency (gram_correction_e9 observed_e9_squared)

/-! ## §1 — Structural X² + structural Gram correction -/

/-- `X² = alphaInv_213_e9²` at e18 scale.  This is the
    **213-internal** base for the structural Gram correction —
    NO observed α appears. -/
def X_squared_e18 : Nat := alphaInv_213_e9 * alphaInv_213_e9

/-- ★★★★★ **Structural Gram correction at e9** — Newton-1 from y₀ = X.

    `gram_correction_structural := 10²⁷ / (25 · X²)`

    The Newton update on `f(y) = 25y³ + 10²⁷ − 25Xy²` at y = X
    gives `y₁ = X − f(X)/f'(X) = X − 10²⁷/(25X²)`.  Hence the
    structural Gram correction `X − y₁` is exactly this expression.

    This is the **213-internal replacement** for the
    self-referential `gram_correction_e9 := 10²⁷ / (25·observed²)`. -/
def gram_correction_structural : Nat :=
  cubic_one_e27 / (25 * X_squared_e18)

/-- Concrete value of `X_squared_e18`. -/
theorem X_squared_value :
    X_squared_e18 = 137036001241 * 137036001241 := by rfl

/-- ★★★★★ **Structural Gram correction = 2130** at e9 scale.

    The Newton-1 step from X = 137,036,001,241 gives a structural
    Gram correction that **exactly matches** the observed-based
    value (both = 2130) at e9 precision.  This is the strongest
    possible numerical agreement at the cubic-root level. -/
theorem gram_correction_structural_value :
    gram_correction_structural = 2130 := by decide

/-! ## §2 — Comparison: structural vs observed-based -/

/-- ★★★★★★ **Structural Gram = observed-based Gram** at e9 scale.

  The Newton-1-from-X iteration produces a structural Gram
  correction `2130` matching the observed-based correction `2130`
  exactly.  This is the structural confirmation that the cubic
  root y₀(X) is well-approximated by Newton-1, and the difference
  X² vs observed² at e9 precision is below rounding threshold. -/
theorem structural_equals_observed_at_e9 :
    gram_correction_e9 = gram_correction_structural := by decide

/-- The Newton iteration gives `X − y₁ = 2130` at e9 scale, so
    the predicted `1/α_em(structural) × 10⁹` is
    `X − 2130 = 137,036,001,241 − 2130 = 137,035,999,111`. -/
def alphaInv_structural_e9 : Nat := alphaInv_213_e9 - gram_correction_structural

theorem alphaInv_structural_value :
    alphaInv_structural_e9 = 137035999111 := by
  show alphaInv_213_e9 - gram_correction_structural = 137035999111
  rw [gram_correction_structural_value]
  decide

/-- The structural prediction is within 27 × 10⁻⁹ of CODATA. -/
theorem structural_vs_observed_27 :
    alphaInv_structural_e9 = observed_e9 + 27 := by
  show alphaInv_213_e9 - gram_correction_structural = observed_e9 + 27
  rw [gram_correction_structural_value]
  decide

/-! ## §3 — The structural derivation has removed observed-α -/

/-- ★★★★★★ **Structural derivation: NO observed-α in RHS**

  `gram_correction_structural = 10²⁷ / (25 · X²)` where
  `X = alphaInv_213_e9` is the 5-layer base formula at e9 scale —
  **derived from atomic principles** (π², π⁵, NS, NT, d, α_GUT).

  In contrast, `gram_correction_e9` uses `observed_e9` (CODATA
  measurement) on the RHS.  The structural form replaces this
  self-referential element with a purely 213-internal expression,
  giving the **same value 2130** at e9 precision.

  Resulting precision: `alphaInv_structural_e9 = observed_e9 + 27`,
  i.e., **27 × 10⁻⁹ ≈ 0.2 ppb** structural-derivation accuracy —
  identical to the observed-based post-Gram residual.

  This achieves the **Phase 3 goal**: structural Gram correction
  derived from 213-internal data only.  The remaining 27 × 10⁻⁹
  residual is the **Phase 4 target** (next-order Dyson tail). -/
theorem newton_structural_eliminates_observed_alpha :
    -- Structural correction at e9
    gram_correction_structural = 2130
    -- Structural prediction for 1/α_em at e9
    ∧ alphaInv_structural_e9 = 137035999111
    -- Residual to CODATA: 27 × 10⁻⁹ ≈ 0.2 ppb
    ∧ alphaInv_structural_e9 = observed_e9 + 27
    -- Exact agreement with observed-based at e9
    ∧ gram_correction_e9 = gram_correction_structural
    -- Structural form uses only alphaInv_213_e9 (no observed_e9)
    ∧ gram_correction_structural = cubic_one_e27 / (25 * X_squared_e18) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gram_correction_structural_value
  · exact alphaInv_structural_value
  · exact structural_vs_observed_27
  · exact structural_equals_observed_at_e9
  · rfl

/-! ## §4 — Phase 3 capstone -/

/-- ★★★★★★★ **Phase 3: Newton-from-X structural Gram closure**

  Replaces the self-referential `gram_correction_e9` with a
  213-internal Newton iteration on the cubic `25y³ + 10²⁷ = 25Xy²`
  starting from y₀ = X.  The Newton-1 step gives
  `y₁ = X − 10²⁷/(25X²)`, and the deduced Gram correction
  `X − y₁ = 10²⁷/(25X²) = 2130` matches the observed-based 2130
  **exactly** at e9 scale.

  The structural prediction `1/α_em × 10⁹ = 137,035,999,111`
  agrees with CODATA `137,035,999,084` to within **27 × 10⁻⁹**
  (≈ 0.2 ppb), achieving precision-theorem-quality accuracy
  with NO observed α in the RHS.

  Phase 3 → Phase 4: the remaining 27 × 10⁻⁹ residual is the
  next-order Dyson tail (per `StructuralGap.lean` candidate
  corrections).  Further Newton iterations are NOT needed at e9
  precision — the residual is a structural higher-order effect
  outside the cubic. -/
theorem phase3_newton_close :
    -- Structural Gram = Newton-1 from X
    gram_correction_structural = cubic_one_e27 / (25 * X_squared_e18)
    -- Value at e9 scale
    ∧ gram_correction_structural = 2130
    -- Exactly matches observed-based at e9 precision
    ∧ gram_correction_e9 = gram_correction_structural
    -- Structural 1/α_em prediction
    ∧ alphaInv_structural_e9 = 137035999111
    -- Accuracy: 27 × 10⁻⁹ ≈ 0.2 ppb
    ∧ alphaInv_structural_e9 = observed_e9 + 27
    -- 213-internal: only alphaInv_213_e9 appears in derivation
    ∧ X_squared_e18 = alphaInv_213_e9 * alphaInv_213_e9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact gram_correction_structural_value
  · exact structural_equals_observed_at_e9
  · exact alphaInv_structural_value
  · exact structural_vs_observed_27
  · rfl

end E213.Lib.Physics.AlphaEM.GramStructuralNewton
