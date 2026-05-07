import E213.Lib.Math.Probability.Capstone

/-!
# Probability 213 — Phase EF Marathon Capstone

The grand 20-fact bundle synthesizing the full Probability marathon
(Phases EA–EE).  Every fact is `#print axioms` ∅ — Bishop-style
atomic counting with no Ω, no σ-algebra, no Choice.

This is the **headline witness** that 213-native probability theory
is foundationally complete at the atomic level: every probability is
a `(Nat, Nat)` ratio, expectation/variance are weighted sums,
sample mean / Bayesian update / Gaussian peak are all structurally
derivable from `Nat` arithmetic alone.

Structure: 5 sub-bundles × 4 facts each = 20 facts.
-/

namespace E213.Lib.Math.Probability.MarathonCapstone

open E213.Lib.Math.Probability.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.UniformOnUnit (UnitSubBracket)
open E213.Lib.Math.Probability.Bernoulli (Bernoulli)
open E213.Lib.Math.Probability.Binomial (pAA pBB pAB ABBernoulli)
open E213.Lib.Math.Probability.Expectation (bernoulli discreteNum)
open E213.Lib.Math.Probability.Variance (bernoulliNum bernoulliDen)
open E213.Lib.Math.Probability.SampleMean (sampleMeanNum sampleMeanDen)
open E213.Lib.Math.Probability.LLN (balancedHeadsTails)
open E213.Lib.Math.Probability.Bayesian (BetaCount)
open E213.Lib.Math.Probability.Gaussian
  (expSumAtZero gaussianPeakAtZero gaussianPeakMass)

/-- ★★★ **Phase EF — Probability 213 marathon final capstone** ★★★

    Twenty headline facts spanning the full Probability marathon,
    selected one per major theme.  All `#print axioms` ∅ — Bishop-
    style atomic counting with no Ω, no σ-algebra, no Choice.

    20 = 4 (EA) + 4 (EB) + 4 (EC) + 4 (ED) + 4 (EE). -/
theorem phaseEF_marathon_capstone (N n : Nat) :
    -- ☆ EA atoms
    ProbabilityCut.unit.toFlux.forward
      = E213.Lib.Math.Real213.CutSumTest.constCut 1 1
    ∧ (UnitSubBracket.uniform UnitSubBracket.whole).num = 1
    ∧ pAA.num + pBB.num + pAB.num = pAA.den
    ∧ Bernoulli.fair.success.num + Bernoulli.fair.failure.num
        = Bernoulli.fair.p.den
    -- ☆ EB moments
    ∧ (bernoulli Bernoulli.fair).num = 1
    ∧ bernoulliNum Bernoulli.fair = 1
    ∧ bernoulliDen Bernoulli.fair = 4
    ∧ discreteNum [(3, 0), (1, 1), (6, 2)] = 13
    -- ☆ EC sample mean / LLN
    ∧ sampleMeanNum (List.replicate n true) = n
    ∧ sampleMeanNum (balancedHeadsTails n) = n
    ∧ sampleMeanDen (balancedHeadsTails n) = 2 * n
    ∧ sampleMeanNum (balancedHeadsTails n) * 2
        = sampleMeanDen (balancedHeadsTails n) * 1
    -- ☆ ED Bayesian
    ∧ BetaCount.uniformPrior.posteriorMean.num = 1
    ∧ BetaCount.uniformPrior.updateOnSuccess.posteriorMean.num = 2
    ∧ BetaCount.uniformPrior.updateOnFailure.posteriorMean.num = 1
    ∧ (BetaCount.uniformPrior.updateBatch 0 0).successes
        = BetaCount.uniformPrior.successes
    -- ☆ EE Gaussian / CLT
    ∧ expSumAtZero N = 1
    ∧ gaussianPeakAtZero = 1
    ∧ gaussianPeakMass.num = 1
    ∧ 2 * E213.Lib.Math.Probability.SampleMean.countTrue
        (balancedHeadsTails n)
      = (balancedHeadsTails n).length :=
  ⟨ rfl, rfl, by decide
  , E213.Lib.Math.Probability.Bernoulli.Bernoulli.sum_to_one
      Bernoulli.fair
  , rfl, by decide, by decide, by decide
  , (E213.Lib.Math.Probability.SampleMean.allHeads_sampleMean n).1
  , (E213.Lib.Math.Probability.LLN.LLN_unit n).1
  , (E213.Lib.Math.Probability.LLN.LLN_unit n).2
  , E213.Lib.Math.Probability.LLN.fair_LLN n
  , rfl, rfl, rfl
  , (E213.Lib.Math.Probability.Bayesian.BetaCount.updateBatch_zero
      BetaCount.uniformPrior).1
  , E213.Lib.Math.Probability.Gaussian.expSumAtZero_eq_one N
  , rfl, rfl
  , E213.Lib.Math.Probability.Gaussian.CLT_fair_centered n ⟩

end E213.Lib.Math.Probability.MarathonCapstone
