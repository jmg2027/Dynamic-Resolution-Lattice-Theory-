import E213.Lib.Math.Probability.Expectation
import E213.Lib.Math.Probability.Binomial

/-!
# Probability — `Variance`

Variance as **atomic squared spread**.

For Bernoulli with success `p` and failure `1 − p` (indicator `X ∈ {0, 1}`):
  `Var[X] = p · (1 − p)` = `success.num · failure.num / den²`.

For a discrete distribution with values `v_i` and masses `m_i / D`:
  `E[X²] = (Σ m_i · v_i²) / D`,  `Var[X] = E[X²] − (E[X])²`.

213-native: variance is just two `Nat` arithmetic primitives —
`successNum · failureNum` (numerator) and `den²` (denominator).
-/

namespace E213.Lib.Math.Probability.Variance

open E213.Lib.Math.Probability.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Bernoulli (Bernoulli)
open E213.Lib.Math.Probability.Expectation (discreteNum)

/-- Bernoulli variance numerator: `success.num · failure.num`. -/
def bernoulliNum (b : Bernoulli) : Nat :=
  b.success.num * b.failure.num

/-- Bernoulli variance denominator: `den²`. -/
def bernoulliDen (b : Bernoulli) : Nat :=
  b.p.den * b.p.den

/-- Numerator equality: `bernoulliNum b = num · (den − num)` (rfl). -/
theorem bernoulliNum_eq (b : Bernoulli) :
    bernoulliNum b = b.p.num * (b.p.den - b.p.num) := rfl

/-- Fair coin variance: `1/4`. -/
theorem fair_variance_num : bernoulliNum Bernoulli.fair = 1 := by decide
theorem fair_variance_den : bernoulliDen Bernoulli.fair = 4 := by decide

/-- Certain Bernoulli variance numerator = 0 (`p · 0 = 0`). -/
theorem certain_variance_num : bernoulliNum Bernoulli.certain = 0 := rfl

/-- Impossible Bernoulli variance numerator = 0 (`0 · q = 0`). -/
theorem impossible_variance_num : bernoulliNum Bernoulli.impossible = 0 := rfl

/-- Discrete second moment numerator: `Σ m_i · v_i²`. -/
def discreteSecondMomentNum : List (Nat × Nat) → Nat
  | [] => 0
  | (m, v) :: rest => m * (v * v) + discreteSecondMomentNum rest

/-- Empty second-moment numerator = 0 (rfl). -/
theorem discreteSecondMomentNum_nil :
    discreteSecondMomentNum [] = 0 := rfl

/-- **K_{3,2} second moment**: AA→0, BB→1, AB→2.
    `Σ m·v² = 3·0 + 1·1 + 6·4 = 25` over `D = 10`. -/
theorem K32_secondMoment_num :
    discreteSecondMomentNum [(3, 0), (1, 1), (6, 2)] = 25 := by decide

/-- **AB-indicator second moment** = AB-indicator first moment
    (since indicator squared = indicator). -/
theorem AB_indicator_secondMoment_eq_firstMoment :
    discreteSecondMomentNum [(3, 0), (1, 0), (6, 1)]
      = discreteNum [(3, 0), (1, 0), (6, 1)] := by decide

/-- **AB-indicator variance numerator** (Bernoulli view, `p = 6/10`):
    `success · failure = 6 · 4 = 24`, denominator = 100. -/
theorem AB_indicator_variance :
    bernoulliNum E213.Lib.Math.Probability.Binomial.ABBernoulli = 24
    ∧ bernoulliDen E213.Lib.Math.Probability.Binomial.ABBernoulli = 100 :=
  ⟨by decide, by decide⟩

end E213.Lib.Math.Probability.Variance
