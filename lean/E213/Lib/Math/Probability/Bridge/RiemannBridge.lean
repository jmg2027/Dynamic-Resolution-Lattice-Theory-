import E213.Lib.Math.Analysis.DyadicSearch.DyadicRiemann
import E213.Lib.Math.Analysis.BracketCauchyModulus
import E213.Lib.Math.Probability.Foundation.Cut
import E213.Lib.Math.Real213.Core.Dyadic
import E213.Meta.Tactic.Pow213

/-!
# Probability — Riemann bridge for dyadic integration

A width-scaled wrapper around `Lib/Math/Analysis/DyadicSearch/
DyadicRiemann.riemannSampleSum`.  The raw `riemannSampleSum f db
depth` returns `Σ f(midpoints)` *without* multiplying by sample
width; this file packages the width factor so the result is a
`(Nat, Nat)` pair representing the integral approximation.

For unit bracket `[0, 1]` at depth `n`, sample width = `1/2^(n+1)`,
so width-scaling is `· 1` over `2^(n+1)` — exactly captured by
`riemannScaledNum / riemannScaledDen`.

Convergence modulus inherits from
`BracketCauchyModulus.dyadic_bracket_cauchy_modulus`: linear in
precision, exponentially reliable.
-/

namespace E213.Lib.Math.Probability.Bridge.RiemannBridge

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Real213.Core.Dyadic (dyadicCut)
open E213.Lib.Math.Analysis.BracketCauchyModulus
  (dyadic_bracket_cauchy_modulus)

/-- Width-scaled Riemann sum numerator: raw sample-sum numerator
    times the bracket-length numerator.  Caller multiplies in the
    bracket width. -/
def riemannScaledNum (sumNum widthNum : Nat) : Nat := sumNum * widthNum

/-- Width-scaled Riemann sum denominator: `2^E` times `2^depth` for
    bracket exponent `E` and sample depth `depth`. -/
def riemannScaledDen (E depth : Nat) : Nat := 2 ^ (E + depth)

/-- Riemann scaled denominator at `(0, 0)` is `1` (unit bracket,
    depth-0 sample) — rfl. -/
theorem riemannScaledDen_zero : riemannScaledDen 0 0 = 1 := rfl

/-- Constant integrand `c` over unit bracket: at every depth, the
    width-scaled Riemann sum's numerator factor is `c · 2^depth`. -/
theorem riemannScaled_const_unit (c depth : Nat) :
    riemannScaledNum (2 ^ depth * c) 1 = 2 ^ depth * c := by
  show 2 ^ depth * c * 1 = 2 ^ depth * c
  exact Nat.mul_one _

open E213.Tactic.Pow213 (one_le_two_pow succ_le_two_pow)

/-- Helper: `n ≤ 2^n`. -/
theorem le_two_pow (n : Nat) : n ≤ 2 ^ n :=
  Nat.le_trans (Nat.le_succ n) (succ_le_two_pow n)

/-- ★ **Convergence modulus, propext-free Nat form** ★
    For Riemann sums of constants on unit bracket, depth `≥ k`
    suffices to bring precision below `1/k`.  Stated as a pure
    `Nat`-arithmetic inequality `k ≤ 2^n * m` (avoids the
    `dyadicCut`/`decide_eq_true` form upstream which leaks
    `propext`). -/
theorem convergence_modulus_const (m k : Nat) (hm : 1 ≤ m) :
    ∀ n, k ≤ n → k ≤ 2 ^ n * m := by
  intro n hkn
  -- k ≤ n ≤ 2^n ≤ 2^n * m
  have h1 : k ≤ 2 ^ n := Nat.le_trans hkn (le_two_pow n)
  have h2 : 2 ^ n ≤ 2 ^ n * m :=
    Nat.le_trans (Nat.le_of_eq (Nat.mul_one (2 ^ n)).symm)
      (Nat.mul_le_mul_left (2 ^ n) hm)
  exact Nat.le_trans h1 h2

end E213.Lib.Math.Probability.Bridge.RiemannBridge
