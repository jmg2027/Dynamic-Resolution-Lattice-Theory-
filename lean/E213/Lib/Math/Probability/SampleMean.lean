import E213.Lib.Math.Probability.Bernoulli

/-!
# Probability — Phase EC-1: `SampleMean`

The sample mean as **atomic frequency counting**.

For a `List Bool` outcome of `n` Bernoulli trials,
  `sampleMeanNum = #{true outcomes}`,  `sampleMeanDen = n = list length`.

Closed forms:
  * all-heads of length `n` → mean = `n/n = 1`;
  * all-tails of length `n` → mean = `0/n = 0`;
  * balanced 2n (n heads, n tails) → mean = `n/(2n) = 1/2`.

213-native: no limits, no σ-algebra.  Just `Nat` counts of `Bool`s.
-/

namespace E213.Lib.Math.Probability.SampleMean

/-- Count of `true` outcomes in a Bool list. -/
def countTrue : List Bool → Nat
  | [] => 0
  | true :: rest => 1 + countTrue rest
  | false :: rest => countTrue rest

/-- Sample mean numerator: count of successes. -/
def sampleMeanNum (xs : List Bool) : Nat := countTrue xs

/-- Sample mean denominator: total trials = list length. -/
def sampleMeanDen (xs : List Bool) : Nat := xs.length

/-- 213-native: `(List.replicate n b).length = n`.  Term mode, no
    propext (Lean core's `List.length_replicate` simp-derives via
    propext). -/
theorem length_replicate (b : Bool) : ∀ n,
    (List.replicate n b).length = n
  | 0 => rfl
  | n+1 => by
    show (List.replicate n b).length + 1 = n + 1
    rw [length_replicate b n]

/-- All-heads: `countTrue (replicate n true) = n`. -/
theorem countTrue_allHeads : ∀ n, countTrue (List.replicate n true) = n
  | 0 => rfl
  | n+1 => by
    show 1 + countTrue (List.replicate n true) = n + 1
    rw [countTrue_allHeads n, Nat.add_comm]

/-- All-tails: `countTrue (replicate n false) = 0`. -/
theorem countTrue_allTails : ∀ n, countTrue (List.replicate n false) = 0
  | 0 => rfl
  | n+1 => countTrue_allTails n

/-- All-heads sample mean = `n/n` (numerator and denominator both `n`). -/
theorem allHeads_sampleMean (n : Nat) :
    sampleMeanNum (List.replicate n true) = n
    ∧ sampleMeanDen (List.replicate n true) = n :=
  ⟨countTrue_allHeads n, length_replicate true n⟩

/-- All-tails sample mean = `0/n`. -/
theorem allTails_sampleMean (n : Nat) :
    sampleMeanNum (List.replicate n false) = 0
    ∧ sampleMeanDen (List.replicate n false) = n :=
  ⟨countTrue_allTails n, length_replicate false n⟩

/-- Two trials, all heads: mean = 2/2 (decide). -/
theorem two_heads_mean :
    sampleMeanNum [true, true] = 2 ∧ sampleMeanDen [true, true] = 2 :=
  ⟨by decide, by decide⟩

/-- Balanced [true, false]: mean = 1/2 (decide). -/
theorem balanced_two_mean :
    sampleMeanNum [true, false] = 1 ∧ sampleMeanDen [true, false] = 2 :=
  ⟨by decide, by decide⟩

/-- Balanced [true, true, false, false]: mean = 2/4. -/
theorem balanced_four_mean :
    sampleMeanNum [true, true, false, false] = 2
    ∧ sampleMeanDen [true, true, false, false] = 4 :=
  ⟨by decide, by decide⟩

end E213.Lib.Math.Probability.SampleMean
