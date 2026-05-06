import E213.Lib.Math.Probability.Cut
import E213.Term.Tactic.Nat213

/-!
# Probability — Phase EA-3: `Bernoulli`

The atomic two-outcome distribution: `P(X = 1) = p`, `P(X = 0) = 1 − p`.

A `Bernoulli` is just a `ProbabilityCut` `p`, with `failure = p.complement`.
The two outcomes always sum to 1 — `success.num + failure.num = p.den`.

213-native: no Ω, no random variable, no measure.  Just two atomic
masses whose numerators sum to the common denominator.
-/

namespace E213.Lib.Math.Probability.Bernoulli

open E213.Lib.Math.Probability.Cut (ProbabilityCut)

/-- Bernoulli distribution with success probability `p = num/den`. -/
structure Bernoulli where
  p : ProbabilityCut

namespace Bernoulli

/-- Success outcome: `P(X = 1) = p`. -/
def success (b : Bernoulli) : ProbabilityCut := b.p

/-- Failure outcome: `P(X = 0) = 1 − p` (complement of `p`). -/
def failure (b : Bernoulli) : ProbabilityCut := b.p.complement

/-- Fair coin: `p = 1/2`. -/
def fair : Bernoulli where
  p :=
    { num := 1
      den := 2
      den_pos := Nat.zero_lt_succ 1
      mass_le := Nat.le_succ 1 }

/-- Certain success: `p = 1/1`. -/
def certain : Bernoulli where
  p := ProbabilityCut.unit

/-- Impossible: `p = 0/1`. -/
def impossible : Bernoulli where
  p := ProbabilityCut.zero

/-- **Two-outcome closure**: success and failure numerators sum to the
    common denominator (= total mass 1). -/
theorem sum_to_one (b : Bernoulli) :
    (b.success).num + (b.failure).num = b.p.den :=
  E213.Tactic.Nat213.add_sub_of_le b.p.mass_le

/-- Success and failure share the denominator (rfl). -/
theorem success_failure_same_den (b : Bernoulli) :
    (b.success).den = (b.failure).den := rfl

/-- `failure` is the complement of `success` by construction (rfl). -/
theorem failure_eq_complement (b : Bernoulli) :
    b.failure = b.success.complement := rfl

/-- Fair coin: success numerator = failure numerator = 1 (rfl). -/
theorem fair_balanced :
    fair.success.num = 1 ∧ fair.failure.num = 1 := ⟨rfl, rfl⟩

end Bernoulli

end E213.Lib.Math.Probability.Bernoulli
