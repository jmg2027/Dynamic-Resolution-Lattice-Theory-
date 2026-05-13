import E213.Lib.Math.Probability.Foundation.Bernoulli

/-!
# Probability — `Binomial` (atomic K_{3,2} counting)

Independent Bernoulli trials as **atomic counting**.

Two views:

  * **K_{3,2} pair distribution**: 10 pairs in `Physics.Substrate.Pairs`
    classify as 3 AA + 1 BB + 6 AB.  These three numerators give a
    natural categorical distribution; the AB-or-not collapse yields
    an atomic Bernoulli with `p = 6/10`.

  * **n-trial product mass**: probability of a specific `List Bool`
    outcome under independent Bernoulli trials, computed by atomic
    multiplication.  No σ-algebra, no Choice — just product counting.
-/

namespace E213.Lib.Math.Probability.Distribution.Binomial

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Foundation.Bernoulli (Bernoulli)

/-- AA-pair atomic mass: 3/10 (within big block, K_{3,2}). -/
def pAA : ProbabilityCut where
  num := 3
  den := 10
  den_pos := Nat.zero_lt_succ 9
  mass_le := by decide

/-- BB-pair atomic mass: 1/10 (within small block). -/
def pBB : ProbabilityCut where
  num := 1
  den := 10
  den_pos := Nat.zero_lt_succ 9
  mass_le := by decide

/-- AB-pair atomic mass: 6/10 (cross-block bipartite). -/
def pAB : ProbabilityCut where
  num := 6
  den := 10
  den_pos := Nat.zero_lt_succ 9
  mass_le := by decide

/-- **K_{3,2} pair total**: 3 + 1 + 6 = 10 (atomic counting closure). -/
theorem pair_total : pAA.num + pBB.num + pAB.num = pAA.den := by decide

/-- **AB-or-not Bernoulli**: collapse the categorical pair distribution
    to a Bernoulli with success = "AB-pair", `p = 6/10`. -/
def ABBernoulli : Bernoulli where
  p := pAB

/-- AB-failure mass = 4/10 (AA + BB combined). -/
theorem AB_failure_num : ABBernoulli.failure.num = 4 := rfl

/-- AB-failure equals the AA + BB combined numerator. -/
theorem AB_failure_eq_AA_plus_BB :
    ABBernoulli.failure.num = pAA.num + pBB.num := by decide

/-- Product numerator of an n-trial Bernoulli sequence (atomic count). -/
def trialSequenceNum (b : Bernoulli) : List Bool → Nat
  | [] => 1
  | true :: rest => b.success.num * trialSequenceNum b rest
  | false :: rest => b.failure.num * trialSequenceNum b rest

/-- Common denominator across `n` independent trials: `den^n`. -/
def trialSequenceDen (b : Bernoulli) (n : Nat) : Nat := b.p.den ^ n

/-- Empty trial sequence has numerator 1 (rfl). -/
theorem trialSequenceNum_nil (b : Bernoulli) :
    trialSequenceNum b [] = 1 := rfl

/-- Two fair-coin heads: numerator = 1·1 = 1. -/
theorem fair_two_heads :
    trialSequenceNum Bernoulli.fair [true, true] = 1 := by decide

/-- Two fair-coin tails: numerator = 1·1 = 1 (failure num = 1). -/
theorem fair_two_tails :
    trialSequenceNum Bernoulli.fair [false, false] = 1 := by decide

/-- Fair coin n=2 denominator = 2² = 4. -/
theorem fair_two_den :
    trialSequenceDen Bernoulli.fair 2 = 4 := by decide

end E213.Lib.Math.Probability.Distribution.Binomial
