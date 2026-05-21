import E213.Lib.Math.Probability.Foundation.Expectation
import E213.Lib.Math.Probability.Distribution.Binomial

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

namespace E213.Lib.Math.Probability.Foundation.Variance

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Foundation.Bernoulli (Bernoulli)
open E213.Lib.Math.Probability.Foundation.Expectation (discreteNum)

/-- Bernoulli variance numerator: `success.num · failure.num`. -/
def bernoulliNum (b : Bernoulli) : Nat :=
  b.success.num * b.failure.num

/-- Bernoulli variance denominator: `den²`. -/
def bernoulliDen (b : Bernoulli) : Nat :=
  b.p.den * b.p.den

/-- Discrete second moment numerator: `Σ m_i · v_i²`. -/
def discreteSecondMomentNum : List (Nat × Nat) → Nat
  | [] => 0
  | (m, v) :: rest => m * (v * v) + discreteSecondMomentNum rest

/-- ★ Variance master — Bernoulli formula identity (rfl), fair-coin
    1/4 closure, certain/impossible degenerate cases, discrete
    second-moment empty rfl, K_{3,2} pair second moment 25/10,
    AB-indicator second moment = first moment (since indicator² =
    indicator), AB-indicator Bernoulli variance 24/100.
    STRICT ∅-AXIOM. -/
theorem variance_master :
    -- Bernoulli numerator identity (rfl)
    (∀ b : Bernoulli, bernoulliNum b = b.p.num * (b.p.den - b.p.num))
    -- Fair coin variance 1/4
    ∧ bernoulliNum Bernoulli.fair = 1
    ∧ bernoulliDen Bernoulli.fair = 4
    -- Degenerate cases: certain / impossible have variance numerator 0
    ∧ bernoulliNum Bernoulli.certain = 0
    ∧ bernoulliNum Bernoulli.impossible = 0
    -- Discrete second moment identities
    ∧ discreteSecondMomentNum [] = 0
    -- K_{3,2} second moment: AA→0, BB→1, AB→2 ⇒ 25/10
    ∧ discreteSecondMomentNum [(3, 0), (1, 1), (6, 2)] = 25
    -- AB-indicator second moment = first moment (indicator² = indicator)
    ∧ discreteSecondMomentNum [(3, 0), (1, 0), (6, 1)]
        = discreteNum [(3, 0), (1, 0), (6, 1)]
    -- AB-indicator Bernoulli variance: 24/100
    ∧ bernoulliNum E213.Lib.Math.Probability.Distribution.Binomial.ABBernoulli = 24
    ∧ bernoulliDen E213.Lib.Math.Probability.Distribution.Binomial.ABBernoulli = 100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; rfl
  all_goals decide

end E213.Lib.Math.Probability.Foundation.Variance
