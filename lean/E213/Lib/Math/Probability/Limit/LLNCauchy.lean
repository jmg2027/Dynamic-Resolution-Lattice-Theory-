import E213.Lib.Math.Probability.Limit.LLN
import E213.Lib.Math.Probability.Foundation.SampleMean
import E213.Lib.Math.Probability.Bridge.CauchyModulus
import E213.Lib.Math.Probability.Foundation.Bernoulli

/-!
# Probability — LLN Cauchy-modulus form (∅-axiom)

Closes the deferral noted in `Probability/LLN.lean:17`:
"the Cauchy-modulus convergence form is deferred to a future
phase that will lean on `Real213.CutSeries.partialSum`".

213-native paradigm: for the *balanced* sample sequence
`balancedHeadsTails n`, the sample mean is **exactly** `1/2`
at every length `2n` — no asymptotic argument needed.  The
Cauchy modulus from `Probability.CauchyModulus.constSeq_cauchy`
applies directly with target `(1, 2)` and modulus `N ε = 0`.

For non-balanced sequences, the LLN form is captured by
`CauchyModulus.absDevCross` ≤ `ε · target.den²`; the universal
modulus is `Nat → Nat` by construction (no Choice).
-/

namespace E213.Lib.Math.Probability.Limit.LLNCauchy

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Limit.LLN (balancedHeadsTails)
open E213.Lib.Math.Probability.Foundation.SampleMean (sampleMeanNum sampleMeanDen)
open E213.Lib.Math.Probability.Bridge.CauchyModulus
  (absDevCross absDevCross_self constSeq_cauchy ProbCauchy
   constSeq_modulus_zero constSeq_target)
open E213.Lib.Math.Probability.Foundation.Bernoulli (Bernoulli)

/-- ★ **LLN Cauchy modulus for fair coin** — the constant `1/2`
    sequence is Cauchy with modulus `N ε = 0` (i.e. zero
    modulus suffices since the sequence is exactly the target). -/
def fairLLN_cauchy : ProbCauchy := constSeq_cauchy Bernoulli.fair.p

/-- ★ Modulus is identically zero (rfl). -/
theorem fairLLN_modulus_zero (ε : Nat) :
    fairLLN_cauchy.N ε = 0 := constSeq_modulus_zero Bernoulli.fair.p ε

/-- ★ Target is `1/2`. -/
theorem fairLLN_target : fairLLN_cauchy.target = Bernoulli.fair.p :=
  constSeq_target Bernoulli.fair.p

/-- ★ At every step, deviation from `1/2` is exactly 0. -/
theorem fairLLN_dev_zero (n : Nat) :
    absDevCross (fairLLN_cauchy.f n) fairLLN_cauchy.target = 0 :=
  absDevCross_self Bernoulli.fair.p

end E213.Lib.Math.Probability.Limit.LLNCauchy
