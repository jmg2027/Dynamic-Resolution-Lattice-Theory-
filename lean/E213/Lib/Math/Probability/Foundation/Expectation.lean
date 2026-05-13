import E213.Lib.Math.Probability.Foundation.Bernoulli

/-!
# Probability — `Expectation`

Expected value as **atomic weighted counting**.

For a Bernoulli with success probability `p`, indicator `X ∈ {0, 1}`:
  `E[X] = 1 · p + 0 · (1 − p) = p`.

For a discrete distribution `[(mass_i, value_i)]` with common denominator
`D`, the expected value's numerator is `Σ mass_i · value_i` over `D`.

213-native: no integral, no σ-algebra.  Just weighted sums of `Nat`s.
-/

namespace E213.Lib.Math.Probability.Foundation.Expectation

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Foundation.Bernoulli (Bernoulli)

/-- Bernoulli expectation: `E[X] = p` (success probability). -/
def bernoulli (b : Bernoulli) : ProbabilityCut := b.success

/-- Fair coin expectation = 1/2 (rfl). -/
theorem bernoulli_fair_num : (bernoulli Bernoulli.fair).num = 1 := rfl

/-- Fair coin expectation denominator = 2 (rfl). -/
theorem bernoulli_fair_den : (bernoulli Bernoulli.fair).den = 2 := rfl

/-- Certain Bernoulli: `E[X] = 1` (rfl). -/
theorem bernoulli_certain_num : (bernoulli Bernoulli.certain).num = 1 := rfl

/-- Impossible Bernoulli: `E[X] = 0` (rfl). -/
theorem bernoulli_impossible_num : (bernoulli Bernoulli.impossible).num = 0 := rfl

/-- Discrete expectation numerator: `Σ mass_i · value_i` for a list of
    (mass-numerator, value) pairs with common denominator `D`. -/
def discreteNum : List (Nat × Nat) → Nat
  | [] => 0
  | (m, v) :: rest => m * v + discreteNum rest

/-- Discrete expectation `E[X] = (Σ mass_i · value_i) / D`. -/
def discrete (D : Nat) (xs : List (Nat × Nat)) : Nat × Nat :=
  (discreteNum xs, D)

/-- Empty list expectation numerator = 0 (rfl). -/
theorem discreteNum_nil : discreteNum [] = 0 := rfl

/-- Singleton: `E[X] = m·v / D`. -/
theorem discreteNum_singleton (m v : Nat) :
    discreteNum [(m, v)] = m * v := by
  show m * v + 0 = m * v
  exact Nat.add_zero (m * v)

/-- **K_{3,2} pair expectation**: assign values AA→0, BB→1, AB→2.
    `E[X] = (3·0 + 1·1 + 6·2) / 10 = 13/10`. -/
theorem K32_expectation_num :
    discreteNum [(3, 0), (1, 1), (6, 2)] = 13 := by decide

/-- **AB-or-not expectation** = 6/10 (the AB-pair Bernoulli mass). -/
theorem AB_indicator_expectation_num :
    discreteNum [(3, 0), (1, 0), (6, 1)] = 6 := by decide

end E213.Lib.Math.Probability.Foundation.Expectation
