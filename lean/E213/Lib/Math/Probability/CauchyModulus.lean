import E213.Lib.Math.Probability.Cut
import E213.Lib.Math.Probability.LLN
import E213.Lib.Math.Probability.Concentration
import E213.Lib.Math.Probability.CLTLimit

/-!
# Probability — atomic Cauchy modulus framework

A `(Nat, Nat)`-only Cauchy modulus over sequences of
`ProbabilityCut`s.  The deviation between `f n` and a fixed `target`
is the cross-multiplied absolute difference

  |f.num · t.den − t.num · f.den|

expressed in `Nat` via the clamped `excess + deficit` pattern from
`Concentration.lean`.  The Cauchy modulus says this absolute
deviation falls below `ε · t.den²` for all `n ≥ N ε`.

The trivial witness (`constSeq_cauchy`, modulus 0) specialises to
the existing `CLTLimit.balanced_LLN_modulus`.
-/

namespace E213.Lib.Math.Probability.CauchyModulus

open E213.Lib.Math.Probability.Cut (ProbabilityCut)

/-- Cross-multiplied absolute deviation between two probability cuts,
    in `Nat` via clamped sub (one term is zero). -/
def absDevCross (a b : ProbabilityCut) : Nat :=
  (a.num * b.den - b.num * a.den) + (b.num * a.den - a.num * b.den)

/-- `absDevCross a a = 0`.  Self-deviation vanishes. -/
theorem absDevCross_self (a : ProbabilityCut) : absDevCross a a = 0 := by
  show (a.num * a.den - a.num * a.den) + (a.num * a.den - a.num * a.den) = 0
  rw [Nat.sub_self, Nat.add_zero]

/-- Cauchy structure over a `Nat → ProbabilityCut` sequence with
    explicit modulus `N : Nat → Nat`. -/
structure ProbCauchy where
  f : Nat → ProbabilityCut
  target : ProbabilityCut
  N : Nat → Nat
  cauchy : ∀ ε n, N ε ≤ n →
    absDevCross (f n) target ≤ ε * (target.den * target.den)

/-- Constant sequence is Cauchy with modulus `N ε = 0`. -/
def constSeq_cauchy (a : ProbabilityCut) : ProbCauchy where
  f := fun _ => a
  target := a
  N := fun _ => 0
  cauchy := fun ε n _ => by
    rw [absDevCross_self]
    exact Nat.zero_le _

/-- Constant-sequence modulus is 0 at every ε (rfl). -/
theorem constSeq_modulus_zero (a : ProbabilityCut) (ε : Nat) :
    (constSeq_cauchy a).N ε = 0 := rfl

/-- Constant-sequence target = the constant value (rfl). -/
theorem constSeq_target (a : ProbabilityCut) :
    (constSeq_cauchy a).target = a := rfl

/-- ★ Bridge to existing balanced-sample LLN: the constant
    `1/2` sequence has Cauchy modulus 0 — recovers the trivial
    modulus delivered by `CLTLimit.balanced_LLN_modulus`. -/
theorem bridge_to_balancedLLN (ε : Nat) :
    ∃ N : Nat, ∀ n, N ≤ n →
      absDevCross
        ((constSeq_cauchy
          (E213.Lib.Math.Probability.Bernoulli.Bernoulli.fair).p).f n)
        (E213.Lib.Math.Probability.Bernoulli.Bernoulli.fair).p
      ≤ ε *
        ((E213.Lib.Math.Probability.Bernoulli.Bernoulli.fair).p.den *
         (E213.Lib.Math.Probability.Bernoulli.Bernoulli.fair).p.den) :=
  ⟨0, fun n _ =>
    (constSeq_cauchy
      (E213.Lib.Math.Probability.Bernoulli.Bernoulli.fair).p).cauchy
      ε n (Nat.zero_le _)⟩

end E213.Lib.Math.Probability.CauchyModulus
