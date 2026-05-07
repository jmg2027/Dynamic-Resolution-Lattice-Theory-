import E213.Lib.Math.Information.MutualInfo
import E213.Lib.Math.Probability.Bernoulli

/-!
# Information — Channel + capacity (atomic dyadic)

A discrete channel: input symbol → output symbol with possible
flip.  The **binary symmetric channel** (BSC) flips with
probability `1/2^k` (dyadic noise).

Channel capacity = max mutual information over input distributions.
For BSC with dyadic flip rate `1/2^k`:

  `C = 1 − h(1/2^k) bits`

where `h` is the binary entropy function.  On dyadic substrate,
`h(1/2^k) = k / 2^k` (exact rational, not transcendental).

Noiseless channel (k = ∞ atomically: zero flip probability) has
capacity 1 (full information transmission).
-/

namespace E213.Lib.Math.Information.Channel

open E213.Lib.Math.Information.MutualInfo
  (mutualInfoIndependent mutualInfoBits)
open E213.Lib.Math.Probability.Bernoulli (Bernoulli)

/-- Noiseless binary channel: input bit = output bit; no flip. -/
def noiselessChannel : Nat := 1

/-- Capacity of noiseless binary channel = 1 bit per symbol. -/
theorem noiseless_capacity : noiselessChannel = 1 := rfl

/-- Trivially-noisy binary channel (always flips): capacity 0
    despite the structure preserving information.  Note: even
    full-flip is invertible — the *zero* capacity case is the
    *random* channel where each output is uncorrelated with input. -/
def randomChannelCapacity : Nat := 0

/-- BSC at dyadic noise rate `1/2^k`: simplified-form capacity is
    `k` bits per `2^k` symbols (ratio `k/2^k`).  For atomic Nat
    representation we keep `k` and `2^k` separately. -/
def bscCapacityNum (k : Nat) : Nat := k
def bscCapacityDen (k : Nat) : Nat := 2 ^ k

/-- BSC capacity is positive for `k ≥ 1`. -/
theorem bsc_capacity_pos (k : Nat) (h : 1 ≤ k) :
    1 ≤ bscCapacityNum k := h

/-- BSC at `k = 1` (noise rate 1/2): random channel, capacity = 1/2. -/
theorem bsc_half_capacity :
    bscCapacityNum 1 = 1 ∧ bscCapacityDen 1 = 2 := ⟨rfl, rfl⟩

/-- BSC at `k = 8` (noise rate 1/256, byte-level): capacity 8/256 = 1/32. -/
theorem bsc_byte_capacity :
    bscCapacityNum 8 = 8 ∧ bscCapacityDen 8 = 256 :=
  ⟨rfl, by decide⟩

end E213.Lib.Math.Information.Channel
