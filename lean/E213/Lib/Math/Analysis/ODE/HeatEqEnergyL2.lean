import E213.Lib.Math.Analysis.ODE.HeatEqDiscrete
import E213.Lib.Math.Foundations.Positivity

/-!
# Discrete heat equation — pointwise L²-Jensen (convexity) bounds (∅-axiom)

**Marathon P3** (`research-notes/frontiers/pde_estimates/discrete_pde_estimates_ladder.md`).

The heat step is a **convex average** of neighbour values, so by Jensen / convexity of the
square it cannot increase the L² norm pointwise:

  * non-lazy `(½,½)`:  `(a+b)² ≤ 2(a²+b²)`,
  * lazy `(¼,½,¼)`:    `(a+2b+c)² ≤ 4(a²+2b²+c²)`.

These are the pointwise L²-dissipation seeds — the energy-method companion of the L∞
maximum principle (`HeatEqDiscrete`).  Worked over ℤ (the clean ring for squares) with the
**POSITIVITY archetype** (`Foundations/Positivity`): each gap is an explicit sum of squares,
discharged by `ring_intZ` + `positivity_of_sq`/`positivity_of_sq3` — exactly the `amgm_2`
pattern.  Summing over the grid (Int `gridSum`) would give the L² energy contraction; that
summation is P3's remaining analytic step (the signed Dirichlet form, blocked on a stronger
∅-axiom multivariate ring normalizer — see the ladder note).

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.ODE.HeatEqEnergyL2

open E213.Meta.Int213
open E213.Lib.Math.Foundations.Positivity (positivity_of_sq positivity_of_sq3)

/-- ★★★ **L²-Jensen, non-lazy (2-point average).**  `(a+b)² ≤ 2(a²+b²)` over ℤ; the gap is
    the single square `(a−b)²`.  The post-step value `heatStepNum = a+b` has its square bounded
    by twice the neighbour energy — heat does not increase the (averaged) L² norm pointwise. -/
theorem heatStep_l2_jensen (a b : Int) :
    (a + b) * (a + b) ≤ 2 * (a * a + b * b) := by
  have hgap : 2 * (a * a + b * b) - (a + b) * (a + b) = (a - b) * (a - b) := by ring_intZ
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero (positivity_of_sq _ _ hgap))

/-- ★★★ **L²-Jensen, lazy (3-point `(¼,½,¼)` average).**  `(a+2b+c)² ≤ 4(a²+2b²+c²)` over ℤ;
    the gap is the sum of squares `(a−2b+c)² + (a−c)² + (a−c)²`.  The lazy post-step value
    `lazyHeatStepNum = a+2b+c` has its square bounded by four times the weighted neighbour
    energy — the smoothing stencil's L²-dissipation. -/
theorem lazyHeatStep_l2_jensen (a b c : Int) :
    (a + 2 * b + c) * (a + 2 * b + c) ≤ 4 * (a * a + 2 * (b * b) + c * c) := by
  have hgap : 4 * (a * a + 2 * (b * b) + c * c) - (a + 2 * b + c) * (a + 2 * b + c)
      = (a - 2 * b + c) * (a - 2 * b + c) + (a - c) * (a - c) + (a - c) * (a - c) := by
    ring_intZ
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero (positivity_of_sq3 _ _ _ _ hgap))

end E213.Lib.Math.Analysis.ODE.HeatEqEnergyL2
