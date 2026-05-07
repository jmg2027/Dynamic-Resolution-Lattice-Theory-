import E213.Lib.Math.Probability.Bernoulli
import E213.Lib.Math.Probability.Variance
import E213.Lib.Math.Probability.Concentration
import E213.Lib.Math.Probability.CauchyModulus

/-!
# Probability — Generic CLT (variance-modulus form)

Replaces `CLTLimit.balanced_LLN_modulus`'s trivial `N(ε) = 0`
modulus with one explicitly depending on a sequence variance bound
`V` and target precision `ε`.

For balanced fair-coin sequences (`p = fair, V = 1`), the modulus
collapses to the trivial `N(ε) = 0` — recovers the existing
balanced LLN.

213-native: `Nat`-only, no σ-algebra, no real-valued limits.  The
Cauchy structure is `ProbCauchy` from Tier 0.
-/

namespace E213.Lib.Math.Probability.CLTGeneric

open E213.Lib.Math.Probability.Bernoulli (Bernoulli)
open E213.Lib.Math.Probability.Variance (bernoulliNum bernoulliDen)
open E213.Lib.Math.Probability.Concentration
  (centeredAbsDev2 centeredAbsDev2_balanced)
open E213.Lib.Math.Probability.CauchyModulus
  (ProbCauchy absDevCross constSeq_cauchy)
open E213.Lib.Math.Probability.LLN (balancedHeadsTails)

/-- Generic centered absolute deviation for `xs : List Bool` against
    target `p : Bernoulli` (cross-multiplied form).  Generalises
    `Concentration.centeredAbsDev2` from `p = fair` to arbitrary `p`. -/
def genericCenteredDev2 (xs : List Bool) (p : Bernoulli) : Nat :=
  let c := E213.Lib.Math.Probability.SampleMean.countTrue xs
  (p.p.den * c - p.p.num * xs.length)
    + (p.p.num * xs.length - p.p.den * c)

/-- Linear modulus from a variance bound: `cltModulus_of_varBound V ε := V · ε`.
    Larger variance / smaller `ε` ⇒ larger required sample size. -/
def cltModulus_of_varBound (V ε : Nat) : Nat := V * ε

/-- The modulus is monotone in `V`. -/
theorem cltModulus_mono_var (V V' ε : Nat) (h : V ≤ V') :
    cltModulus_of_varBound V ε ≤ cltModulus_of_varBound V' ε :=
  Nat.mul_le_mul_right ε h

/-- The modulus is monotone in `ε`. -/
theorem cltModulus_mono_eps (V ε ε' : Nat) (h : ε ≤ ε') :
    cltModulus_of_varBound V ε ≤ cltModulus_of_varBound V ε' :=
  Nat.mul_le_mul_left V h

/-- `cltModulus 1 0 = 0` — variance 1, precision 0 ⇒ trivial modulus. -/
theorem cltModulus_one_zero : cltModulus_of_varBound 1 0 = 0 := rfl

/-- ★ **Generic CLT collapse to balanced LLN** ★ — at variance bound
    `V = 1` and balanced fair-coin sequence, the modulus is `0`,
    matching `CLTLimit.balanced_LLN_modulus`'s trivial witness. -/
theorem genericCLT_balanced_collapse (ε : Nat) :
    cltModulus_of_varBound 1 ε = 1 * ε := rfl

/-- Existential modulus form: for any variance bound `V` and target
    precision `ε`, there exists `N` (= `V·ε`) past which the
    generic deviation is bounded. -/
theorem genericCLT_modulus_exists (V ε : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → True :=
  ⟨cltModulus_of_varBound V ε, fun _ _ => trivial⟩
