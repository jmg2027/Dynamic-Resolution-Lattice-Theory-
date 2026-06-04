import E213.Lib.Math.Probability.Foundation.SampleMean
import E213.Meta.Tactic.List213

/-!
# Probability — Law of Large Numbers (atomic)

The 213-native LLN, atomic (no limit, no σ-algebra):

  *for any balanced length-`2n` Boolean sample, sample mean = `1/2`
  exactly.*

Generalization for an arbitrary Bernoulli `b = num/den`:

  *if `countTrue · den = length · num` (empirical = theoretical),
  then `sampleMean = E[X]`.*

This makes frequency-Lens and expectation-Lens readings agree structurally at balance.
The Cauchy-modulus convergence form is deferred to a future phase
that will lean on `Real213.CutSeries.partialSum`.
-/

namespace E213.Lib.Math.Probability.Limit.LLN

open E213.Lib.Math.Probability.Foundation.SampleMean
  (countTrue sampleMeanNum sampleMeanDen length_replicate)
open E213.Tactic.List213 (length_append)

/-- `countTrue` distributes over append. -/
theorem countTrue_append : ∀ xs ys : List Bool,
    countTrue (xs ++ ys) = countTrue xs + countTrue ys
  | [], ys => (Nat.zero_add (countTrue ys)).symm
  | true :: xs, ys => by
    show 1 + countTrue (xs ++ ys) = 1 + countTrue xs + countTrue ys
    rw [countTrue_append xs ys, Nat.add_assoc]
  | false :: xs, ys => countTrue_append xs ys

/-- A *balanced* length-`2n` Boolean sequence: `n` heads then `n` tails. -/
def balancedHeadsTails (n : Nat) : List Bool :=
  List.replicate n true ++ List.replicate n false

/-- Balanced sample has exactly `n` heads. -/
theorem balanced_countTrue (n : Nat) :
    countTrue (balancedHeadsTails n) = n := by
  show countTrue (List.replicate n true ++ List.replicate n false) = n
  rw [countTrue_append,
      E213.Lib.Math.Probability.Foundation.SampleMean.countTrue_allHeads,
      E213.Lib.Math.Probability.Foundation.SampleMean.countTrue_allTails,
      Nat.add_zero]

/-- Balanced sample has length `2n`. -/
theorem balanced_length (n : Nat) :
    (balancedHeadsTails n).length = 2 * n := by
  show (List.replicate n true ++ List.replicate n false).length = 2 * n
  rw [length_append, length_replicate, length_replicate, Nat.two_mul]

/-- ★ **LLN_unit** ★ — balanced fair-coin sample of length `2n` has
    sample mean exactly `n / (2n) = 1/2`. -/
theorem LLN_unit (n : Nat) :
    sampleMeanNum (balancedHeadsTails n) = n
    ∧ sampleMeanDen (balancedHeadsTails n) = 2 * n :=
  ⟨balanced_countTrue n, balanced_length n⟩

/-- **Bernoulli LLN, exact form**: when empirical count matches the
    theoretical ratio (`countTrue · den = length · num`), the sample
    mean *equals* `E[X]` (cross-multiplication form). -/
theorem bernoulli_LLN_exact (xs : List Bool) (num den : Nat)
    (h : countTrue xs * den = xs.length * num) :
    sampleMeanNum xs * den = sampleMeanDen xs * num := h

/-- LLN for fair coin (`p = 1/2`): balanced sample satisfies the LLN
    cross-product `n · 2 = 2n · 1`. -/
theorem fair_LLN (n : Nat) :
    sampleMeanNum (balancedHeadsTails n) * 2
      = sampleMeanDen (balancedHeadsTails n) * 1 := by
  rw [(LLN_unit n).1, (LLN_unit n).2, Nat.mul_one, Nat.mul_comm 2 n]

end E213.Lib.Math.Probability.Limit.LLN
