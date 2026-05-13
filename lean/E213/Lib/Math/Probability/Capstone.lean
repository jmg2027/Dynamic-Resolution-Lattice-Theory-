import E213.Lib.Math.Probability.Cut
import E213.Lib.Math.Probability.UniformOnUnit
import E213.Lib.Math.Probability.Bernoulli
import E213.Lib.Math.Probability.Binomial
import E213.Lib.Math.Probability.Expectation
import E213.Lib.Math.Probability.Variance
import E213.Lib.Math.Probability.SampleMean
import E213.Lib.Math.Probability.LLN
import E213.Lib.Math.Probability.Bayesian
import E213.Lib.Math.Probability.Gaussian
import E213.Lib.Math.Probability.Independence
import E213.Lib.Math.Probability.Markov
import E213.Lib.Math.Probability.Concentration
import E213.Lib.Math.Probability.BetaDensity
import E213.Lib.Math.Probability.CLTLimit
import E213.Lib.Math.Probability.CauchyModulus
import E213.Lib.Math.Probability.RiemannBridge
import E213.Lib.Math.Probability.Chebyshev
import E213.Lib.Math.Probability.BetaNormalized
import E213.Lib.Math.Probability.CLTGeneric
import E213.Lib.Math.Probability.Hoeffding
import E213.Lib.Math.Cohomology.CutExpFiniteTruncation
import E213.Lib.Math.Cohomology.CutLog
import E213.Lib.Math.Probability.ChernoffGrade

/-!
# Probability — synthesis bundles

Six closure-fact bundles, one per topical cluster, plus a final
total-witness bundling all five clusters into one ∅-axiom theorem.

Topical bundles:

  * `atoms_witness`        — Cut / Uniform / Bernoulli / Binomial (4)
  * `moments_witness`      — Expectation / Variance (4)
  * `sampleMean_witness`   — SampleMean / LLN (4)
  * `bayesian_witness`     — BetaCount / posteriorMean (4)
  * `gaussian_witness`     — Gaussian peak / CLT centering (4)

Total witness:

  * `total_witness`        — 20-fact grand bundle (4 per cluster).

Every theorem is `#print axioms` ∅ — Bishop-style atomic counting,
no Ω, no σ-algebra, no Choice.  Every probability is a `(Nat, Nat)`
ratio.
-/

namespace E213.Lib.Math.Probability.Capstone

open E213.Lib.Math.Probability.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.UniformOnUnit (UnitSubBracket)
open E213.Lib.Math.Probability.Bernoulli (Bernoulli)
open E213.Lib.Math.Probability.Binomial
  (pAA pBB pAB ABBernoulli trialSequenceNum trialSequenceDen)

/-- ★ **Atomic-probability synthesis** ★ — Cut/Uniform/Bernoulli/Binomial.

    Closure facts:
      1. unit's forward leg = `constCut 1 1`;
      2. zero's forward leg = `constCut 0 1`;
      3. uniform mass on whole unit = `1/1`;
      4. K_{3,2} pair total: `3 + 1 + 6 = 10`;
      5. fair-coin two-heads atomic product. -/
theorem atoms_witness :
    -- (1) unit forward leg
    ProbabilityCut.unit.toFlux.forward
      = E213.Lib.Math.Real213.Sum.CutSumTest.constCut 1 1
    -- (2) zero forward leg
    ∧ ProbabilityCut.zero.toFlux.forward
        = E213.Lib.Math.Real213.Sum.CutSumTest.constCut 0 1
    -- (3) uniform on whole unit = 1/1
    ∧ (UnitSubBracket.uniform UnitSubBracket.whole).num = 1
    ∧ (UnitSubBracket.uniform UnitSubBracket.whole).den = 1
    -- (4) K_{3,2} pair total
    ∧ pAA.num + pBB.num + pAB.num = pAA.den
    -- (5) fair-coin two-heads
    ∧ trialSequenceNum Bernoulli.fair [true, true] = 1
    ∧ trialSequenceDen Bernoulli.fair 2 = 4 :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

/-- ★ **Moments synthesis** ★ — Expectation + Variance.

    Closure facts:
      1. fair-coin `E[X] = 1/2`;
      2. impossible Bernoulli `E[X] = 0`;
      3. K_{3,2} discrete expectation numerator = `13` (D = 10);
      4. fair-coin `Var[X] = 1/4`;
      5. AB-indicator `Var = 24/100 = p(1−p)`;
      6. AB-indicator second moment = first moment (X² = X). -/
theorem moments_witness :
    -- (1) fair-coin E[X]
    (E213.Lib.Math.Probability.Expectation.bernoulli Bernoulli.fair).num = 1
    ∧ (E213.Lib.Math.Probability.Expectation.bernoulli Bernoulli.fair).den = 2
    -- (2) impossible E[X] = 0
    ∧ (E213.Lib.Math.Probability.Expectation.bernoulli Bernoulli.impossible).num = 0
    -- (3) K_{3,2} expectation numerator
    ∧ E213.Lib.Math.Probability.Expectation.discreteNum
        [(3, 0), (1, 1), (6, 2)] = 13
    -- (4) fair-coin Var[X]
    ∧ E213.Lib.Math.Probability.Variance.bernoulliNum Bernoulli.fair = 1
    ∧ E213.Lib.Math.Probability.Variance.bernoulliDen Bernoulli.fair = 4
    -- (5) AB-indicator Var
    ∧ E213.Lib.Math.Probability.Variance.bernoulliNum ABBernoulli = 24
    -- (6) AB-indicator second moment = first moment
    ∧ E213.Lib.Math.Probability.Variance.discreteSecondMomentNum
        [(3, 0), (1, 0), (6, 1)]
      = E213.Lib.Math.Probability.Expectation.discreteNum
        [(3, 0), (1, 0), (6, 1)] :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- ★ **Sample-mean / LLN synthesis** ★.

    Closure facts:
      1. all-heads of length `n` → numerator = `n`, denominator = `n`;
      2. all-tails of length `n` → numerator = `0`;
      3. balanced-heads-tails of length `2n` → numerator = `n`;
      4. balanced-heads-tails length = `2n`;
      5. fair-coin LLN cross-product (`n · 2 = 2n · 1`). -/
theorem sampleMean_witness (n : Nat) :
    -- (1) all-heads
    E213.Lib.Math.Probability.SampleMean.sampleMeanNum
        (List.replicate n true) = n
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanDen
        (List.replicate n true) = n
    -- (2) all-tails numerator
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanNum
        (List.replicate n false) = 0
    -- (3-4) balanced sample
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanNum
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) = n
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanDen
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) = 2 * n
    -- (5) fair-coin LLN cross-product
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanNum
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) * 2
      = E213.Lib.Math.Probability.SampleMean.sampleMeanDen
          (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) * 1 :=
  ⟨(E213.Lib.Math.Probability.SampleMean.allHeads_sampleMean n).1,
   (E213.Lib.Math.Probability.SampleMean.allHeads_sampleMean n).2,
   (E213.Lib.Math.Probability.SampleMean.allTails_sampleMean n).1,
   (E213.Lib.Math.Probability.LLN.LLN_unit n).1,
   (E213.Lib.Math.Probability.LLN.LLN_unit n).2,
   E213.Lib.Math.Probability.LLN.fair_LLN n⟩

/-- ★ **Bayesian conjugate synthesis** ★ — BetaCount / posteriorMean.

    Closure facts:
      1. uniform prior posterior mean = `1/2`;
      2. uniform + 1 success → posterior `2/3` (Laplace's rule);
      3. uniform + 1 failure → posterior `1/3` (symmetric);
      4. `updateBatch 0 0` is a no-op on count fields. -/
theorem bayesian_witness :
    -- (1-2) uniform prior posterior mean
    E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.posteriorMean.num = 1
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.posteriorMean.den = 2
    -- (3) Laplace one success → 2/3
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateOnSuccess.posteriorMean.num
        = 2
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateOnSuccess.posteriorMean.den
        = 3
    -- (4) Laplace one failure → 1/3
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateOnFailure.posteriorMean.num
        = 1
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateOnFailure.posteriorMean.den
        = 3
    -- (5) zero batch is no-op
    ∧ (E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateBatch 0 0).successes
        = E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.successes :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
   (E213.Lib.Math.Probability.Bayesian.BetaCount.updateBatch_zero
     E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior).1⟩

/-- ★ **Gaussian peak / CLT synthesis** ★.

    Closure facts:
      1. Taylor `exp` partial sum at `0` = `1` for every order `N`;
      2. Gaussian peak value at `x = 0` = `1`;
      3. Gaussian peak as `ProbabilityCut`: `num = 1`;
      4. CLT centering: `2 · countTrue` (balanced 2n) = `length`;
      5. CLT variance marker: `4 · (count · 2) = length · 4`. -/
theorem gaussian_witness (N n : Nat) :
    -- (1) Taylor exp(0) = 1
    E213.Lib.Math.Probability.Gaussian.expSumAtZero N = 1
    -- (2) Gaussian peak = 1
    ∧ E213.Lib.Math.Probability.Gaussian.gaussianPeakAtZero = 1
    -- (3) Gaussian peak ProbabilityCut numerator
    ∧ E213.Lib.Math.Probability.Gaussian.gaussianPeakMass.num = 1
    -- (4) CLT centering
    ∧ 2 * E213.Lib.Math.Probability.SampleMean.countTrue
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n)
      = (E213.Lib.Math.Probability.LLN.balancedHeadsTails n).length
    -- (5) CLT variance marker
    ∧ 4 * (E213.Lib.Math.Probability.SampleMean.countTrue
            (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) * 2)
      = (E213.Lib.Math.Probability.LLN.balancedHeadsTails n).length * 4 :=
  ⟨E213.Lib.Math.Probability.Gaussian.expSumAtZero_eq_one N,
   rfl, rfl,
   E213.Lib.Math.Probability.Gaussian.CLT_fair_centered n,
   E213.Lib.Math.Probability.Gaussian.CLT_fair_variance_marker n⟩

/-- ★★★ **Total witness** ★★★ — 20-fact grand bundle (4 per cluster).

    Selected one headline fact per major theme:
      4 atoms (Cut/Uniform/K_{3,2}/Bernoulli)
      4 moments (E[fair], Var[fair] num/den, K_{3,2} sum)
      4 sample-mean / LLN
      4 Bayesian (uniform prior, Laplace ±, batch zero)
      4 Gaussian / CLT
    All `#print axioms` ∅ — Bishop-style atomic counting only. -/
theorem total_witness (N n : Nat) :
    -- ☆ atoms
    ProbabilityCut.unit.toFlux.forward
      = E213.Lib.Math.Real213.Sum.CutSumTest.constCut 1 1
    ∧ (UnitSubBracket.uniform UnitSubBracket.whole).num = 1
    ∧ pAA.num + pBB.num + pAB.num = pAA.den
    ∧ Bernoulli.fair.success.num + Bernoulli.fair.failure.num
        = Bernoulli.fair.p.den
    -- ☆ moments
    ∧ (E213.Lib.Math.Probability.Expectation.bernoulli
         Bernoulli.fair).num = 1
    ∧ E213.Lib.Math.Probability.Variance.bernoulliNum Bernoulli.fair = 1
    ∧ E213.Lib.Math.Probability.Variance.bernoulliDen Bernoulli.fair = 4
    ∧ E213.Lib.Math.Probability.Expectation.discreteNum
        [(3, 0), (1, 1), (6, 2)] = 13
    -- ☆ sample mean / LLN
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanNum
        (List.replicate n true) = n
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanNum
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) = n
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanDen
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) = 2 * n
    ∧ E213.Lib.Math.Probability.SampleMean.sampleMeanNum
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) * 2
      = E213.Lib.Math.Probability.SampleMean.sampleMeanDen
          (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) * 1
    -- ☆ Bayesian
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.posteriorMean.num = 1
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateOnSuccess.posteriorMean.num = 2
    ∧ E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateOnFailure.posteriorMean.num = 1
    ∧ (E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.updateBatch 0 0).successes
        = E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior.successes
    -- ☆ Gaussian / CLT
    ∧ E213.Lib.Math.Probability.Gaussian.expSumAtZero N = 1
    ∧ E213.Lib.Math.Probability.Gaussian.gaussianPeakAtZero = 1
    ∧ E213.Lib.Math.Probability.Gaussian.gaussianPeakMass.num = 1
    ∧ 2 * E213.Lib.Math.Probability.SampleMean.countTrue
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n)
      = (E213.Lib.Math.Probability.LLN.balancedHeadsTails n).length :=
  ⟨ rfl, rfl, by decide
  , E213.Lib.Math.Probability.Bernoulli.Bernoulli.sum_to_one Bernoulli.fair
  , rfl, by decide, by decide, by decide
  , (E213.Lib.Math.Probability.SampleMean.allHeads_sampleMean n).1
  , (E213.Lib.Math.Probability.LLN.LLN_unit n).1
  , (E213.Lib.Math.Probability.LLN.LLN_unit n).2
  , E213.Lib.Math.Probability.LLN.fair_LLN n
  , rfl, rfl, rfl
  , (E213.Lib.Math.Probability.Bayesian.BetaCount.updateBatch_zero
      E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior).1
  , E213.Lib.Math.Probability.Gaussian.expSumAtZero_eq_one N
  , rfl, rfl
  , E213.Lib.Math.Probability.Gaussian.CLT_fair_centered n ⟩

/-- ★ **Independence / conditional witness** ★ — joint and ratio.

    Closure facts:
      1. `joint a b` numerator factorizes: `a.num · b.num`;
      2. `joint a b` denominator factorizes: `a.den · b.den`;
      3. `joint unit a = a` (numerator);
      4. `joint zero a` numerator = 0;
      5. `joint` commutative (numerator);
      6. `conditionalNum a b = a.num`. -/
theorem independence_witness (a b : ProbabilityCut) :
    (E213.Lib.Math.Probability.Independence.joint a b).num
      = a.num * b.num
    ∧ (E213.Lib.Math.Probability.Independence.joint a b).den
        = a.den * b.den
    ∧ (E213.Lib.Math.Probability.Independence.joint
        ProbabilityCut.unit a).num = a.num
    ∧ (E213.Lib.Math.Probability.Independence.joint
        ProbabilityCut.zero a).num = 0
    ∧ (E213.Lib.Math.Probability.Independence.joint a b).num
        = (E213.Lib.Math.Probability.Independence.joint b a).num
    ∧ E213.Lib.Math.Probability.Independence.conditionalNum a b
        = a.num :=
  ⟨ E213.Lib.Math.Probability.Independence.joint_num a b
  , E213.Lib.Math.Probability.Independence.joint_den a b
  , E213.Lib.Math.Probability.Independence.joint_unit_left_num a
  , E213.Lib.Math.Probability.Independence.joint_zero_left_num a
  , E213.Lib.Math.Probability.Independence.joint_comm_num a b
  , E213.Lib.Math.Probability.Independence.conditionalNum_eq a b ⟩

/-- ★ **Markov / sufficient-statistic witness** ★ — `BetaCount` updates
    are commutative on the count fields; Markov inequality holds for
    discrete distributions. -/
theorem markov_witness (b : E213.Lib.Math.Probability.Bayesian.BetaCount)
    (k₁ f₁ k₂ f₂ : Nat) :
    ((b.updateBatch k₁ f₁).updateBatch k₂ f₂).successes
      = ((b.updateBatch k₂ f₂).updateBatch k₁ f₁).successes
    ∧ ∀ a, ∀ xs : List (Nat × Nat),
        a * E213.Lib.Math.Probability.Markov.tailMassNum a xs
          ≤ E213.Lib.Math.Probability.Markov.tailMomentNum a xs :=
  ⟨E213.Lib.Math.Probability.Markov.updateBatch_comm_successes b k₁ f₁ k₂ f₂,
   E213.Lib.Math.Probability.Markov.markov_inequality⟩

/-- ★ **Concentration witness** ★ — balanced 2n has zero deviation,
    all-heads/all-tails have full bias `n`. -/
theorem concentration_witness (n : Nat) :
    E213.Lib.Math.Probability.Concentration.centeredAbsDev2
      (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) = 0
    ∧ E213.Lib.Math.Probability.Concentration.centeredAbsDev2
        (List.replicate n true) = n
    ∧ E213.Lib.Math.Probability.Concentration.centeredAbsDev2
        (List.replicate n false) = n :=
  ⟨E213.Lib.Math.Probability.Concentration.centeredAbsDev2_balanced n,
   E213.Lib.Math.Probability.Concentration.centeredAbsDev2_allHeads n,
   E213.Lib.Math.Probability.Concentration.centeredAbsDev2_allTails n⟩

/-- ★ **Beta density witness** ★ — Beta(1,1) is uniform; Beta(2,1)
    linear in `p`; uniform-prior posterior at any `p` is `1/1`. -/
theorem beta_density_witness (p : ProbabilityCut) :
    E213.Lib.Math.Probability.BetaDensity.betaNumAt 1 1 p = 1
    ∧ E213.Lib.Math.Probability.BetaDensity.betaDenAt 1 1 p = 1
    ∧ E213.Lib.Math.Probability.BetaDensity.betaNumAt 2 1 p = p.num
    ∧ E213.Lib.Math.Probability.BetaDensity.fromBetaCount
        E213.Lib.Math.Probability.Bayesian.BetaCount.uniformPrior p
      = (1, 1) :=
  ⟨E213.Lib.Math.Probability.BetaDensity.beta_uniform_num p,
   E213.Lib.Math.Probability.BetaDensity.beta_uniform_den p,
   E213.Lib.Math.Probability.BetaDensity.beta_2_1_num p,
   E213.Lib.Math.Probability.BetaDensity.fromBetaCount_uniformPrior p⟩

/-- ★ **CLT-modulus witness** ★ — balanced LLN has trivial Cauchy
    modulus `N(ε) = 0`; deviation is identically zero across n. -/
theorem clt_modulus_witness (n m ε : Nat) :
    (∃ N, ∀ k, N ≤ k →
      E213.Lib.Math.Probability.Concentration.centeredAbsDev2
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails k) ≤ ε)
    ∧ E213.Lib.Math.Probability.Concentration.centeredAbsDev2
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n)
      = E213.Lib.Math.Probability.Concentration.centeredAbsDev2
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails m) :=
  ⟨E213.Lib.Math.Probability.CLTLimit.balanced_LLN_modulus ε,
   E213.Lib.Math.Probability.CLTLimit.balanced_cauchy n m⟩

/-- ★ **Cauchy modulus witness** ★ — `ProbCauchy` constSeq has
    modulus 0 (Tier 0 of Real213 extension program). -/
theorem cauchy_modulus_witness (a : ProbabilityCut) (ε : Nat) :
    (E213.Lib.Math.Probability.CauchyModulus.constSeq_cauchy a).N ε = 0
    ∧ (E213.Lib.Math.Probability.CauchyModulus.constSeq_cauchy a).target = a :=
  ⟨E213.Lib.Math.Probability.CauchyModulus.constSeq_modulus_zero a ε,
   E213.Lib.Math.Probability.CauchyModulus.constSeq_target a⟩

/-- ★ **Chebyshev witness** ★ — polynomial concentration
    via Markov-on-second-moment. -/
theorem chebyshev_witness (a n : Nat) :
    a * E213.Lib.Math.Probability.Markov.tailMassNum a [(1, n * n)]
      ≤ E213.Lib.Math.Probability.Markov.tailMomentNum a [(1, n * n)] :=
  E213.Lib.Math.Probability.Chebyshev.chebyshev_allHeads_witness a n

/-- ★ **Beta normalised witness** ★ — closed-form `B(α, β)` for
    `(1,1), (2,1), (1,2)`. -/
theorem beta_normalized_witness :
    E213.Lib.Math.Probability.BetaNormalized.betaNorm 1 1 = (1, 1)
    ∧ E213.Lib.Math.Probability.BetaNormalized.betaNorm 2 1 = (1, 2)
    ∧ E213.Lib.Math.Probability.BetaNormalized.betaNorm 1 2 = (1, 2) :=
  ⟨rfl, rfl, rfl⟩

/-- ★ **Generic CLT witness** ★ — variance-modulus
    `cltModulus_of_varBound V ε := V · ε`, monotone in V and ε. -/
theorem cltGeneric_witness (V ε : Nat) :
    E213.Lib.Math.Probability.CLTGeneric.cltModulus_of_varBound V ε = V * ε
    ∧ E213.Lib.Math.Probability.CLTGeneric.cltModulus_of_varBound 1 0 = 0 :=
  ⟨rfl, rfl⟩

/-- ★ **Hoeffding witness** ★ — finite-depth Taylor partial sum
    bound + balanced collapse to zero deviation. -/
theorem hoeffding_witness (n : Nat) (negArg : Nat → Nat → Bool) :
    E213.Lib.Math.Probability.Hoeffding.hoeffdingBoundAtDepth negArg 0
      = E213.Lib.Math.Real213.Sum.CutSumTest.constCut 0 1
    ∧ E213.Lib.Math.Probability.Concentration.centeredAbsDev2
        (E213.Lib.Math.Probability.LLN.balancedHeadsTails n) = 0 :=
  ⟨rfl,
   E213.Lib.Math.Probability.Concentration.centeredAbsDev2_balanced n⟩

/-- ★ **Reframe witness: nilpotency** ★ — replaces "Cauchy modulus
    on cutExp" with the structural Grade-6 nilpotency. -/
theorem nilpotency_witness
    (α : E213.Lib.Math.Cohomology.Cochain.Core.Cochain 5 1)
    (i : Fin (E213.Lib.Physics.Simplex.Counts.binom 5 6)) :
    E213.Lib.Math.Cohomology.CutExpFiniteTruncation.cupPow α 6 i = false :=
  E213.Lib.Math.Cohomology.CutExpFiniteTruncation.cupPow_grade_6_zero α i

/-- ★ **Reframe witness: grade-index Chernoff** ★ — replaces
    "continuous Chernoff inf_t" with discrete grade-index closure. -/
theorem grade_chernoff_witness (a : Nat) :
    ∃ (g : E213.Lib.Math.Probability.ChernoffGrade.GradeIndex)
      (xs : List (Nat × Nat)),
      a * E213.Lib.Math.Probability.Markov.tailMassNum a xs
        ≤ E213.Lib.Math.Probability.Markov.tailMomentNum a xs :=
  E213.Lib.Math.Probability.ChernoffGrade.closing_grade_exists a

/-- ★ **Reframe witness: log as cup-inverse** ★ — replaces
    "log via integration" with formal algebraic cup-inverse modulo
    Grade-6 nilpotency. -/
theorem cuplog_witness
    (α : E213.Lib.Math.Cohomology.Cochain.Core.Cochain 5 1) :
    E213.Lib.Math.Cohomology.CutLog.cutLog α 1 = α
    ∧ ∀ i : Fin (E213.Lib.Physics.Simplex.Counts.binom 5 6),
        E213.Lib.Math.Cohomology.CutExpFiniteTruncation.cupPow
          (E213.Lib.Math.Cohomology.CutLog.cutLog α 1) 6 i = false :=
  ⟨rfl,
   E213.Lib.Math.Cohomology.CutLog.cutLog_cup_grade_6_zero α⟩

end E213.Lib.Math.Probability.Capstone
