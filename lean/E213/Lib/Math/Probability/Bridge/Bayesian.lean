import E213.Lib.Math.Probability.Foundation.Cut

/-!
# Probability — Bayesian framework (atomic conjugate)

Beta-Binomial conjugacy as **count addition**.

A `BetaCount` is a pair `(α, β)` of effective successes / failures
seen.  The posterior mean is `α / (α + β)` — a `ProbabilityCut`.
Bayes' update on a single observation is just `+1` to the matching
field.  Batch update is `+k` and `+(n − k)`.

213-native: no continuous Beta density, no integration, no σ-algebra.
Conjugate update = atomic counting addition.  This is the cleanest
form of "frequency = belief" — atomic Lens-pair self-agreement.
-/

namespace E213.Lib.Math.Probability.Bridge.Bayesian

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)

/-- Effective `(α, β)` count of successes / failures, with at least
    one observation (so the posterior mass is well-defined). -/
structure BetaCount where
  successes : Nat
  failures : Nat
  total_pos : 0 < successes + failures

namespace BetaCount

/-- Posterior mean as a probability cut: `α / (α + β)`. -/
def posteriorMean (b : BetaCount) : ProbabilityCut where
  num := b.successes
  den := b.successes + b.failures
  den_pos := b.total_pos
  mass_le := Nat.le_add_right b.successes b.failures

/-- Uniform prior `(1, 1)` — Beta(1, 1) = uniform on [0, 1]. -/
def uniformPrior : BetaCount where
  successes := 1
  failures := 1
  total_pos := Nat.zero_lt_succ 1

/-- Single-success update: `α ← α + 1`. -/
def updateOnSuccess (b : BetaCount) : BetaCount where
  successes := b.successes + 1
  failures := b.failures
  total_pos :=
    Nat.lt_of_lt_of_le b.total_pos
      (Nat.add_le_add_right (Nat.le_succ b.successes) b.failures)

/-- Single-failure update: `β ← β + 1`. -/
def updateOnFailure (b : BetaCount) : BetaCount where
  successes := b.successes
  failures := b.failures + 1
  total_pos :=
    Nat.lt_of_lt_of_le b.total_pos
      (Nat.le_succ (b.successes + b.failures))

/-- Batch update: `(α, β) ← (α + ks, β + fs)`. -/
def updateBatch (b : BetaCount) (ks fs : Nat) : BetaCount where
  successes := b.successes + ks
  failures := b.failures + fs
  total_pos :=
    Nat.lt_of_lt_of_le b.total_pos
      (Nat.add_le_add (Nat.le_add_right b.successes ks)
                       (Nat.le_add_right b.failures fs))

/-- `updateOnSuccess` increments `successes` (rfl). -/
theorem updateOnSuccess_successes (b : BetaCount) :
    b.updateOnSuccess.successes = b.successes + 1 := rfl

/-- `updateOnSuccess` preserves `failures` (rfl). -/
theorem updateOnSuccess_failures (b : BetaCount) :
    b.updateOnSuccess.failures = b.failures := rfl

/-- `updateOnFailure` increments `failures` (rfl). -/
theorem updateOnFailure_failures (b : BetaCount) :
    b.updateOnFailure.failures = b.failures + 1 := rfl

/-- `updateBatch b 0 0` is a no-op on the count fields (rfl). -/
theorem updateBatch_zero (b : BetaCount) :
    (b.updateBatch 0 0).successes = b.successes
    ∧ (b.updateBatch 0 0).failures = b.failures :=
  ⟨Nat.add_zero b.successes, Nat.add_zero b.failures⟩

/-- ★ **Bayesian batch ↔ sequential** ★ — single-success update is
    the same as `updateBatch _ 1 0` (count fields). -/
theorem updateOnSuccess_eq_batch (b : BetaCount) :
    b.updateOnSuccess.successes = (b.updateBatch 1 0).successes
    ∧ b.updateOnSuccess.failures = (b.updateBatch 1 0).failures :=
  ⟨rfl, (Nat.add_zero b.failures).symm⟩

/-- Sequential = batch (count fields): two successes via two updates
    equals one batch with `ks = 2`. -/
theorem two_successes_eq_batch (b : BetaCount) :
    b.updateOnSuccess.updateOnSuccess.successes
    = (b.updateBatch 2 0).successes := by
  show b.successes + 1 + 1 = b.successes + 2
  rw [Nat.add_assoc]

/-- Uniform prior posterior mean = 1/2 (rfl). -/
theorem uniformPrior_posteriorMean :
    uniformPrior.posteriorMean.num = 1
    ∧ uniformPrior.posteriorMean.den = 2 :=
  ⟨rfl, rfl⟩

/-- Posterior after one success on uniform prior: `2/3`
    (Laplace's rule of succession at `n = 1`). -/
theorem laplace_one_success :
    uniformPrior.updateOnSuccess.posteriorMean.num = 2
    ∧ uniformPrior.updateOnSuccess.posteriorMean.den = 3 :=
  ⟨rfl, rfl⟩

/-- Posterior after one failure on uniform prior: `1/3`. -/
theorem laplace_one_failure :
    uniformPrior.updateOnFailure.posteriorMean.num = 1
    ∧ uniformPrior.updateOnFailure.posteriorMean.den = 3 :=
  ⟨rfl, rfl⟩

end BetaCount

end E213.Lib.Math.Probability.Bridge.Bayesian
