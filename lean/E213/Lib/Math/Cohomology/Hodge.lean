import E213.Lib.Math.Cohomology.Hodge.Delta
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone
import E213.Lib.Math.Cohomology.Hodge.InvolutionLifts
import E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Math.Cohomology.Hodge.SignedStarC4
import E213.Lib.Math.Cohomology.Hodge.SignedStarFull
import E213.Lib.Math.Cohomology.Hodge.HodgeRiemannJ

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Hodge`.

  Hodge structure on the 213-native cochain complex — the
  Δ-Laplacian + ⋆-involution machinery, and the signed Hodge ⋆
  carrying the complex structure `ℤ[J] ≅ ℤ[i]` (the CP imaginary unit).

  ## Files

    * `Star`               — Hodge ⋆ at cochain level
    * `Involution`         — involution machinery
    * `InvolutionTemplate` — COH-2 pointwise template
                             `hodge_involution_pointwise_5`
                             used by every Δ⁴ stratum lift
    * `InvolutionLifts`    — `⋆⋆ = id` Prop-lifts at all five
                             Δ⁴ strata (5, 0), (5, 1), (5, 2),
                             (5, 3), (5, 4), plus the all-strata
                             bundle `hodge_involution_5strata_capstone`
    * `InvolutionCapstone` — backward-compat re-export of the
                             all-strata capstone
    * `Delta`              — codifferential `δ* = ⋆δ⋆`
    * `SignedStarC4`       — the signed ⋆ at a grade pair, `⋆² = −1`,
                             `ℤ[J] ≅ ℤ[i]`, `det = a²+b²`, `N(2+i) = 5`
    * `SignedStarFull`     — the full grade-1 `Λ¹(ℝ⁴)` signed ⋆,
                             `⋆² = −1` every direction ⇒ order exactly 4
                             = `C₄` (closes "phase ∈ C₄")
    * `HodgeRiemannJ`      — the Weil operator `J`, `Jᵀ Q J = Q`,
                             `Q·J = I ≻ 0` (Hodge–Riemann positivity)
-/
