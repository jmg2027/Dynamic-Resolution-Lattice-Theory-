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

/-! ## Local energy dissipation — `grad(lazy u) = lazy(grad u)` + Jensen

The heat step commutes with the discrete gradient (constant-coefficient stencil): on four
consecutive grid values `p,q,r,s`, the lazy-step difference `lazyStep(next) − lazyStep(here) =
(s+r) − (q+p)` equals the **lazy stencil applied to the three edge gradients**
`(q−p) + 2(r−q) + (s−r)`.  Jensen (`lazyHeatStep_l2_jensen`) then bounds its square — the pointwise
energy-dissipation inequality whose grid-sum gives `E(lazy u) ≤ 16·E(u)` (shift-invariance turns
each shifted gradient-energy back into `E(u)`; the `Nat`-summation cast is the remaining P3 step). -/

/-- ★★★ **Local energy dissipation (over ℤ).**  For four consecutive grid values `p,q,r,s`,

      `(s+r−q−p)² ≤ 4·((q−p)² + 2(r−q)² + (s−r)²)`.

    The left side is `|lazyStep(next)−lazyStep(here)|²` (an edge of the stepped field); the right
    is `4×` the lazy-weighted sum of the three contributing **gradient** energies.  Direct from
    `lazyHeatStep_l2_jensen` at the gradients `(q−p, r−q, s−r)` (whose lazy combination is exactly
    `s+r−q−p`, by `ring_intZ`).  Summed over the periodic grid this yields `E(lazy u) ≤ 16·E(u)`. -/
theorem lazy_energy_pointwise (p q r s : Int) :
    (s + r - q - p) * (s + r - q - p)
      ≤ 4 * ((q - p) * (q - p) + 2 * ((r - q) * (r - q)) + (s - r) * (s - r)) := by
  have key := lazyHeatStep_l2_jensen (q - p) (r - q) (s - r)
  have hid : (q - p) + 2 * (r - q) + (s - r) = s + r - q - p := by ring_intZ
  rw [hid] at key; exact key

end E213.Lib.Math.Analysis.ODE.HeatEqEnergyL2
