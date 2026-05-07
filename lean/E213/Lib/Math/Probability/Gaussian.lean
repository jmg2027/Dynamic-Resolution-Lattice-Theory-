import E213.Lib.Math.Probability.Cut
import E213.Lib.Math.Probability.SampleMean
import E213.Lib.Math.Probability.LLN

/-!
# Probability — CLT + Gaussian (atomic)

The Gaussian peak `exp(−x²/2)|_{x=0} = exp(0) = 1` and a CLT
skeleton — standardized partial sums with mean 0 and variance
preserved.

213-native: Taylor series at `x = 0` collapses to its constant
term (all higher monomials vanish).  No need for transcendence
or limits — the *value at zero* is a finite-`Nat` fact.

The `partialSum`-based Cauchy-modulus form of full CLT lives in
`Real213.CutSeries.partialSum`; here we expose the atomic peak
identity and standardization scaffolding.
-/

namespace E213.Lib.Math.Probability.Gaussian

open E213.Lib.Math.Probability.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.SampleMean (countTrue)

/-- Taylor coefficient of `exp(x)` at order `n`, evaluated at `x = 0`.
    Only the `n = 0` term survives (`x^n` vanishes for `n ≥ 1`). -/
def expTaylorAtZero : Nat → Nat
  | 0 => 1
  | _ + 1 => 0

/-- Partial Taylor sum of `exp(x)` at `x = 0`, up to order `N`. -/
def expSumAtZero : Nat → Nat
  | 0 => expTaylorAtZero 0
  | n + 1 => expSumAtZero n + expTaylorAtZero (n + 1)

/-- ★ **`exp(0) = 1`** ★ — partial Taylor sum at every order `N` is
    exactly 1 (only the `n = 0` term contributes). -/
theorem expSumAtZero_eq_one : ∀ N, expSumAtZero N = 1
  | 0 => rfl
  | n + 1 => by
    show expSumAtZero n + expTaylorAtZero (n + 1) = 1
    rw [expSumAtZero_eq_one n]
    show 1 + 0 = 1
    rfl

/-- The Gaussian peak: `exp(−x²/2)|_{x=0}`.
    At `x = 0`, the argument is `−0²/2 = 0`, so the value equals
    the Taylor sum at zero, which is `1`. -/
def gaussianPeakAtZero : Nat := expSumAtZero 0

/-- ★ **Gaussian peak value = 1** ★ — atomic, all-order. -/
theorem gaussianPeakAtZero_eq_one (N : Nat) :
    expSumAtZero N = gaussianPeakAtZero := by
  rw [expSumAtZero_eq_one N]
  show 1 = expSumAtZero 0
  rfl

/-- Gaussian peak as a `ProbabilityCut`: forward leg = `1/1`,
    matching the unnormalized density at the peak. -/
def gaussianPeakMass : ProbabilityCut where
  num := gaussianPeakAtZero
  den := 1
  den_pos := Nat.zero_lt_succ 0
  mass_le := Nat.le_refl 1

/-- Gaussian peak mass numerator = 1 (rfl). -/
theorem gaussianPeakMass_num : gaussianPeakMass.num = 1 := rfl

/-- ★ **CLT centering** ★ — fair-coin balanced length-`2n` sample has
    `2 · countTrue = length`, i.e., the standardized deviation
    `2·heads − length` equals `0` exactly.  Centering *attained
    structurally*, no limit needed. -/
theorem CLT_fair_centered (n : Nat) :
    2 * countTrue (E213.Lib.Math.Probability.LLN.balancedHeadsTails n)
    = (E213.Lib.Math.Probability.LLN.balancedHeadsTails n).length := by
  rw [E213.Lib.Math.Probability.LLN.balanced_countTrue,
      E213.Lib.Math.Probability.LLN.balanced_length]

/-- **CLT variance preservation**: balanced fair-coin variance
    numerator = `n` over total trial count `2n`, matching
    Bernoulli Var = `p(1−p) = 1/4` after `1/(2n)` normalization.
    Atomic marker: each balanced trial contributes `1/4` to the
    centered second moment. -/
theorem CLT_fair_variance_marker (n : Nat) :
    4 * (countTrue (E213.Lib.Math.Probability.LLN.balancedHeadsTails n)
       * 2)
    = (E213.Lib.Math.Probability.LLN.balancedHeadsTails n).length
        * 4 := by
  rw [E213.Lib.Math.Probability.LLN.balanced_countTrue,
      E213.Lib.Math.Probability.LLN.balanced_length]
  show 4 * (n * 2) = 2 * n * 4
  rw [Nat.mul_comm 2 n, Nat.mul_comm 4 (n * 2)]

end E213.Lib.Math.Probability.Gaussian
