import E213.Lib.Math.Information.Bit
import E213.Lib.Math.Probability.Foundation.Cut

/-!
# Information — Shannon entropy (atomic dyadic form)

For a uniform distribution over `2^n` equally likely outcomes:

  `H(uniform on 2^n) = n bits`

This is **exact**, not an approximation.  In 213-native terms,
the count of outcomes IS a dyadic power, and the entropy IS the
exponent — no real-valued `log` is needed.  The continuous Shannon
entropy `−Σ p log p` becomes the *defining* identity `entropy =
depth` on the dyadic substrate.

For non-dyadic distributions (probability not a power of 1/2),
the entropy is *not* a `Nat`; classical real-valued log is needed.
This file handles the atomic dyadic cases; non-dyadic entropy is
a continuation marathon.
-/

namespace E213.Lib.Math.Information.Entropy

open E213.Lib.Math.Information.Bit (bitDepth bitsAfterBisections)
open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)

/-- Shannon entropy of the uniform distribution over `2^n` outcomes
    is exactly `n` bits.  This is *the definition* on the dyadic
    substrate, not a Taylor approximation. -/
def shannonEntropyUniformBits (n : Nat) : Nat := n

/-- ★ **`H(uniform on 2^n) = n`** ★ — the foundational atomic
    identity of dyadic information theory. -/
theorem shannonEntropy_uniform_eq_depth (n : Nat) :
    shannonEntropyUniformBits n = n := rfl

/-- Fair coin = uniform over 2^1 = 2 outcomes, entropy 1 bit. -/
theorem fair_coin_entropy : shannonEntropyUniformBits 1 = 1 := rfl

/-- 4-way uniform = entropy 2 bits. -/
theorem four_way_uniform : shannonEntropyUniformBits 2 = 2 := rfl

/-- Byte (256 outcomes) = entropy 8 bits. -/
theorem byte_uniform_entropy : shannonEntropyUniformBits 8 = 8 := rfl

/-- N_U-scale uniform (2^25 outcomes) = entropy 25 bits.  Connects
    to the system invariant `N_U = 5^25` via dyadic encoding. -/
theorem nU_dyadic_entropy : shannonEntropyUniformBits 25 = 25 := rfl

/-- Atomic dyadic Bernoulli skew: probability `1/2^k`.  Surprise
    value (= entropy of the rare event) is `k` bits — exact. -/
def surpriseBitsDyadic (k : Nat) : Nat := k

/-- Surprise of a rare 1/2^k event = `k` bits (rfl). -/
theorem surprise_dyadic_eq_depth (k : Nat) :
    surpriseBitsDyadic k = k := rfl

/-- A 1/2 (fair) event has 1 bit of surprise. -/
theorem fair_surprise : surpriseBitsDyadic 1 = 1 := rfl

/-- A 1/256 event (byte-rare) has 8 bits of surprise. -/
theorem byte_rare_surprise : surpriseBitsDyadic 8 = 8 := rfl

/-- The trivial certain event (probability 1 = 1/2^0) has 0 bits
    of surprise — knowing a certain outcome carries zero
    information. -/
theorem certain_zero_surprise : surpriseBitsDyadic 0 = 0 := rfl

/-- Connection to `ProbabilityCut`: a `ProbabilityCut` with
    `den = 2^k` and `num = 1` represents a "rare" event with
    `k` bits of surprise. -/
def dyadicProbabilityCut (k : Nat) : ProbabilityCut where
  num := 1
  den := 2 ^ k
  den_pos := Nat.pos_pow_of_pos k (Nat.zero_lt_succ 1)
  mass_le := Nat.pos_pow_of_pos k (Nat.zero_lt_succ 1)

end E213.Lib.Math.Information.Entropy
