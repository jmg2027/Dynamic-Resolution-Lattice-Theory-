import E213.Lib.Math.Probability.Foundation.Bernoulli

/-!
# Probability — `Binomial` (atomic K_{3,2} counting)

Independent Bernoulli trials as **atomic counting**.

Two views:

  * **K_{3,2} pair distribution**: 10 pairs in `Physics.AtomicBase.Pairs`
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

/-- **AB-or-not Bernoulli**: collapse the categorical pair distribution
    to a Bernoulli with success = "AB-pair", `p = 6/10`. -/
def ABBernoulli : Bernoulli where
  p := pAB

/-- Product numerator of an n-trial Bernoulli sequence (atomic count). -/
def trialSequenceNum (b : Bernoulli) : List Bool → Nat
  | [] => 1
  | true :: rest => b.success.num * trialSequenceNum b rest
  | false :: rest => b.failure.num * trialSequenceNum b rest

/-- Common denominator across `n` independent trials: `den^n`. -/
def trialSequenceDen (b : Bernoulli) (n : Nat) : Nat := b.p.den ^ n

/-- ★ Binomial master — K_{3,2} pair closure, AB-Bernoulli failure
    identities, fair-coin n=2 trial-sequence numerics. -/
theorem binomial_master :
    -- K_{3,2} pair total: 3 + 1 + 6 = 10
    pAA.num + pBB.num + pAB.num = pAA.den
    -- AB-Bernoulli failure num = 4
    ∧ ABBernoulli.failure.num = 4
    -- AB-failure = AA + BB combined
    ∧ ABBernoulli.failure.num = pAA.num + pBB.num
    -- Empty trial sequence: numerator = 1 (rfl ∀ b)
    ∧ (∀ b : Bernoulli, trialSequenceNum b [] = 1)
    -- Fair coin n = 2 trial-sequence numerics
    ∧ trialSequenceNum Bernoulli.fair [true, true] = 1
    ∧ trialSequenceNum Bernoulli.fair [false, false] = 1
    ∧ trialSequenceDen Bernoulli.fair 2 = 4 := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro _; rfl
  · decide
  · decide
  · decide

end E213.Lib.Math.Probability.Distribution.Binomial
