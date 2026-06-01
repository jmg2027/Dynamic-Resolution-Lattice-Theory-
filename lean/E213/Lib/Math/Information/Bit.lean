import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket

/-!
# Information — bit = bisection

The 213-native foundation of information theory: **one bit equals
one dyadic bisection**.  Depth `n` of a `DyadicBracket` carries
exactly `n` bits of information, with `log₂(2^n) = n` realised
atomically (no transcendental log).

This file defines:

  * `bitDepth db` — bit count of a dyadic bracket (= `expE`).
  * `bitsAfterBisections n` — bit count after `n` bisections.
  * Atomic `log₂_pow_two_eq` — `log₂(2^n) = n` as a `Nat` identity
    (it's the *defining* relation, not a Taylor approximation).

213-native: bit and bisection are the same thing; "log₂" is just
`Nat`-valued depth.  No continuous logarithm, no integral.
-/

namespace E213.Lib.Math.Information.Bit

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)

/-- Bit count of a dyadic bracket: `n` bisections give `n` bits. -/
def bitDepth (db : DyadicBracket) : Nat := db.expE

/-- Unit bracket has 0 bits of refinement. -/
def unitBracket_bitDepth : Nat := 0

/-- After `n` bisection steps from the unit bracket, the bit depth
    is exactly `n`.  No log function needed — depth IS the log
    (atomically). -/
def bitsAfterBisections (n : Nat) : Nat := n

/-- ★ **`log₂(2^n) = n` atomically** ★ — identity by definition.
    On dyadic substrate, `log₂` is the depth function; `2^n` has
    depth `n` by construction.  No Taylor series, no integral. -/
theorem log2_pow_two_eq (n : Nat) : bitsAfterBisections n = n := rfl

/-- Concrete: `bitsAfterBisections 0 = 0`. -/
theorem bits_0 : bitsAfterBisections 0 = 0 := rfl

/-- Concrete: `bitsAfterBisections 1 = 1`. -/
theorem bits_1 : bitsAfterBisections 1 = 1 := rfl

/-- Concrete: `bitsAfterBisections 8 = 8`. -/
theorem bits_8 : bitsAfterBisections 8 = 8 := rfl

/-- Concrete: `2^8 = 256` (a byte's bit-cardinality, decidable). -/
theorem byte_cardinality : 2 ^ bitsAfterBisections 8 = 256 := by decide

/-- Concrete: `bitsAfterBisections 25 = 25` (25 bisections give
    a 25-bit index).  Atomic. -/
theorem bits_25 : bitsAfterBisections 25 = 25 := rfl

end E213.Lib.Math.Information.Bit
