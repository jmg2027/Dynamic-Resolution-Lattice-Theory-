import E213.Lib.Math.Probability.Cut
import E213.Lib.Math.Probability.Bayesian

/-!
# Probability — Beta(α, β) atomic density

Unnormalized Beta density evaluated at an atomic `ProbabilityCut`
`p = num/den`:

  `betaNumAt α β p = num^(α-1) · (den-num)^(β-1)`
  `betaDenAt α β p = den^(α+β-2)`

For α = β = 1 (uniform Beta), `betaNumAt = 1` everywhere — flat density.

Connection to `BetaCount` posterior: a `BetaCount (α, β)` represents
the *parameter* of the Beta posterior; this file evaluates the density
*at a point*.

213-native: continuous density without integration step — atomic
power-product on `(Nat, Nat)` ratios.
-/

namespace E213.Lib.Math.Probability.BetaDensity

open E213.Lib.Math.Probability.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Bayesian (BetaCount)

/-- Beta(α, β) density numerator at `p`: `num^(α-1) · (den-num)^(β-1)`. -/
def betaNumAt (α β : Nat) (p : ProbabilityCut) : Nat :=
  p.num ^ (α - 1) * (p.den - p.num) ^ (β - 1)

/-- Beta(α, β) density denominator at `p`: `den^(α+β-2)`. -/
def betaDenAt (α β : Nat) (p : ProbabilityCut) : Nat :=
  p.den ^ (α + β - 2)

/-- ★ **Beta(1,1) is uniform** ★ — `betaNumAt 1 1 p = 1` for any `p`. -/
theorem beta_uniform_num (p : ProbabilityCut) : betaNumAt 1 1 p = 1 := by
  show p.num ^ (1 - 1) * (p.den - p.num) ^ (1 - 1) = 1
  rw [Nat.sub_self, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]

/-- Beta(1,1) denominator = 1 (anywhere). -/
theorem beta_uniform_den (p : ProbabilityCut) : betaDenAt 1 1 p = 1 := by
  show p.den ^ (1 + 1 - 2) = 1
  rw [Nat.sub_self, Nat.pow_zero]

/-- Beta(2,1) at `p`: `betaNumAt = p.num`, density linear in p. -/
theorem beta_2_1_num (p : ProbabilityCut) : betaNumAt 2 1 p = p.num := by
  show p.num ^ (2 - 1) * (p.den - p.num) ^ (1 - 1) = p.num
  show p.num ^ 1 * (p.den - p.num) ^ 0 = p.num
  rw [Nat.pow_zero, Nat.pow_one, Nat.mul_one]

/-- Beta(1,2) at `p`: density is `(den - num)`, linear in 1−p. -/
theorem beta_1_2_num (p : ProbabilityCut) :
    betaNumAt 1 2 p = p.den - p.num := by
  show p.num ^ (1 - 1) * (p.den - p.num) ^ (2 - 1) = p.den - p.num
  show p.num ^ 0 * (p.den - p.num) ^ 1 = p.den - p.num
  rw [Nat.pow_zero, Nat.pow_one, Nat.one_mul]

/-- View a `BetaCount` as a Beta-density parameter pair — bridge from
    Bayesian conjugate update to point-wise density evaluation. -/
def fromBetaCount (b : BetaCount) (p : ProbabilityCut) : Nat × Nat :=
  (betaNumAt b.successes b.failures p, betaDenAt b.successes b.failures p)

/-- Uniform prior `(1, 1)` density at any `p` is `1/1`. -/
theorem fromBetaCount_uniformPrior (p : ProbabilityCut) :
    fromBetaCount BetaCount.uniformPrior p = (1, 1) := by
  show (betaNumAt 1 1 p, betaDenAt 1 1 p) = (1, 1)
  rw [beta_uniform_num, beta_uniform_den]

end E213.Lib.Math.Probability.BetaDensity
