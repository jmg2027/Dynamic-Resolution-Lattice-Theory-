import E213.Lib.Math.Probability.Cut
import E213.Lib.Math.Probability.UniformOnUnit
import E213.Lib.Math.Probability.Bernoulli
import E213.Lib.Math.Probability.Binomial
import E213.Lib.Math.Probability.Expectation
import E213.Lib.Math.Probability.Variance

/-!
# Probability — Phase EA Capstone

Synthesis bundle for the four foundational atoms:

  * `ProbabilityCut`   — atomic mass `num/den ∈ [0, 1]`.
  * `UnitSubBracket`   — sub-bracket of `[0, 1]`.
  * `Bernoulli`        — two-outcome distribution.
  * `Binomial`         — n-trial product mass + K_{3,2} pair atomic.

All facts are ∅-axiom (verified by `_AxiomScanProbe`).  The capstone
records the closure properties: total mass = 1 across each atom.

Phase EA delivers the **atomic counting = probability** core: no Ω, no
σ-algebra, no Choice — every probability is a `(Nat, Nat)` ratio.
-/

namespace E213.Lib.Math.Probability.Capstone

open E213.Lib.Math.Probability.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.UniformOnUnit (UnitSubBracket)
open E213.Lib.Math.Probability.Bernoulli (Bernoulli)
open E213.Lib.Math.Probability.Binomial
  (pAA pBB pAB ABBernoulli trialSequenceNum trialSequenceDen)

/-- ★ **Phase EA atomic-probability synthesis** ★

    Five closure facts establishing the atomic-counting foundation:

    1. unit's forward leg is constant `1/1`;
    2. zero's forward leg is constant `0/1`;
    3. uniform mass on the whole unit is `1/1`;
    4. K_{3,2} pair total: `3 + 1 + 6 = 10`;
    5. fair-coin two-heads numerator = 1 (atomic product). -/
theorem phaseEA_synthesis :
    -- (1) unit forward leg
    ProbabilityCut.unit.toFlux.forward
      = E213.Lib.Math.Real213.CutSumTest.constCut 1 1
    -- (2) zero forward leg
    ∧ ProbabilityCut.zero.toFlux.forward
        = E213.Lib.Math.Real213.CutSumTest.constCut 0 1
    -- (3) uniform on whole unit = 1/1
    ∧ (UnitSubBracket.uniform UnitSubBracket.whole).num = 1
    ∧ (UnitSubBracket.uniform UnitSubBracket.whole).den = 1
    -- (4) K_{3,2} pair total
    ∧ pAA.num + pBB.num + pAB.num = pAA.den
    -- (5) fair-coin two-heads
    ∧ trialSequenceNum Bernoulli.fair [true, true] = 1
    ∧ trialSequenceDen Bernoulli.fair 2 = 4 :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

/-- ★ **Phase EB expectation/variance synthesis** ★

    Six closure facts on first and second moments:

    1. fair-coin `E[X] = 1/2`;
    2. impossible Bernoulli `E[X] = 0`;
    3. K_{3,2} discrete expectation numerator = 13 (D = 10);
    4. fair-coin `Var[X] = 1/4`;
    5. AB-indicator `Var = 24/100 = p(1−p) = (6·4)/100`;
    6. AB-indicator second moment equals first moment (X² = X). -/
theorem phaseEB_synthesis :
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

end E213.Lib.Math.Probability.Capstone
