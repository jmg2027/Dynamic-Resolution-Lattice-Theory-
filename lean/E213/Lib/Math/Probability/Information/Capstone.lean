import E213.Lib.Math.Probability.Information.Bit
import E213.Lib.Math.Probability.Information.Entropy
import E213.Lib.Math.Probability.Information.MutualInfo
import E213.Lib.Math.Probability.Information.KLDivergence
import E213.Lib.Math.Probability.Information.Channel
import E213.Lib.Math.Probability.Information.Coding

/-!
# Information 213 — Capstone synthesis

Six topical witnesses + one total bundle, all `#print axioms` ∅.

The 213-native foundation of information theory: **bit = bisection**,
log₂(2^n) = n atomically (no real-valued logarithm), Shannon
entropy of uniform on `2^n` is exactly `n` bits, channel capacity
on noiseless dyadic = 1 bit/symbol.
-/

namespace E213.Lib.Math.Probability.Information.Capstone

/-- ★ **Bit witness** ★ — log₂(2^n) = n atomically. -/
theorem bit_witness (n : Nat) :
    E213.Lib.Math.Probability.Information.Bit.bitsAfterBisections n = n :=
  E213.Lib.Math.Probability.Information.Bit.log2_pow_two_eq n

/-- ★ **Entropy witness** ★ — H(uniform on 2^n) = n exactly. -/
theorem entropy_witness (n : Nat) :
    E213.Lib.Math.Probability.Information.Entropy.shannonEntropyUniformBits n = n :=
  E213.Lib.Math.Probability.Information.Entropy.shannonEntropy_uniform_eq_depth n

/-- ★ **Mutual info witness** ★ — independent uniforms ⇒ I = 0. -/
theorem mutualInfo_witness (n m : Nat) :
    E213.Lib.Math.Probability.Information.MutualInfo.mutualInfoIndependent n m = 0 :=
  E213.Lib.Math.Probability.Information.MutualInfo.mutualInfo_independent_zero n m

/-- ★ **KL witness** ★ — self-KL = 0; non-negative everywhere. -/
theorem kl_witness (a b : Nat) :
    E213.Lib.Math.Probability.Information.KLDivergence.klBitsDyadic a a = 0
    ∧ 0 ≤ E213.Lib.Math.Probability.Information.KLDivergence.klBitsDyadic a b :=
  ⟨E213.Lib.Math.Probability.Information.KLDivergence.kl_self_zero a,
   E213.Lib.Math.Probability.Information.KLDivergence.kl_nonneg a b⟩

/-- ★ **Channel witness** ★ — noiseless capacity = 1, BSC(k) = k/2^k. -/
theorem channel_witness (k : Nat) :
    E213.Lib.Math.Probability.Information.Channel.noiselessChannel = 1
    ∧ E213.Lib.Math.Probability.Information.Channel.bscCapacityNum k = k :=
  ⟨rfl, rfl⟩

/-- ★ **Coding witness** ★ — Hamming self-distance 0; optimal
    binary code length = log of alphabet. -/
theorem coding_witness (xs : List Bool) (n : Nat) :
    E213.Lib.Math.Probability.Information.Coding.hammingDistance xs xs = 0
    ∧ E213.Lib.Math.Probability.Information.Coding.optimalCodeLength n = n :=
  ⟨E213.Lib.Math.Probability.Information.Coding.hamming_self xs, rfl⟩

/-- ★★★ **Total witness** ★★★ — 6-fact grand bundle. -/
theorem total_witness (n m k : Nat) (xs : List Bool) :
    E213.Lib.Math.Probability.Information.Bit.bitsAfterBisections n = n
    ∧ E213.Lib.Math.Probability.Information.Entropy.shannonEntropyUniformBits n = n
    ∧ E213.Lib.Math.Probability.Information.MutualInfo.mutualInfoIndependent n m = 0
    ∧ E213.Lib.Math.Probability.Information.KLDivergence.klBitsDyadic n n = 0
    ∧ E213.Lib.Math.Probability.Information.Channel.noiselessChannel = 1
    ∧ E213.Lib.Math.Probability.Information.Coding.hammingDistance xs xs = 0 :=
  ⟨bit_witness n, entropy_witness n, mutualInfo_witness n m,
   (kl_witness n 0).1, (channel_witness k).1,
   (coding_witness xs 0).1⟩

end E213.Lib.Math.Probability.Information.Capstone
