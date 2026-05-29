import E213.Lib.Math.Cohomology.Hodge.Delta
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone
import E213.Lib.Math.Cohomology.Hodge.InvolutionLifts
import E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
import E213.Lib.Math.Cohomology.Hodge.Star

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Hodge`.

  Hodge structure on the 213-native cochain complex — the
  Δ-Laplacian + ⋆-involution machinery.

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
-/
