import E213.Lib.Math.Information.Entropy

/-!
# Information — KL divergence (atomic dyadic)

For two dyadic distributions with surprise depths `a` and `b`:

  `D(p ‖ q) = a − b` (cross-multiplied, clamped Nat sub form).

When `a = b`, the divergence is zero (identical distributions).
When `a > b`, the divergence is positive (p more concentrated
than q on the relevant outcome).

Atomic: subtraction of dyadic depths, no real-valued log ratio.

Jensen's inequality on dyadic substrate becomes the **monotonicity
of `Nat`-subtraction**: `D(p ‖ q) ≥ 0` is just `Nat.zero_le`.
-/

namespace E213.Lib.Math.Information.KLDivergence

open E213.Lib.Math.Information.Entropy (surpriseBitsDyadic)

/-- KL divergence between two dyadic distributions.  Excess depth
    of `p` over `q` (clamped to 0 if reversed). -/
def klBitsDyadic (a b : Nat) : Nat := a - b

/-- Self-KL is zero. -/
theorem kl_self_zero (a : Nat) : klBitsDyadic a a = 0 :=
  Nat.sub_self a

/-- KL is non-negative (Jensen's inequality, atomic Nat form). -/
theorem kl_nonneg (a b : Nat) : 0 ≤ klBitsDyadic a b :=
  Nat.zero_le _

/-- Concrete: KL between fair coin and 1/4 event = 1 bit. -/
theorem kl_fair_to_quarter : klBitsDyadic 2 1 = 1 := rfl

/-- Concrete: KL between byte and bit = 7 bits. -/
theorem kl_byte_to_bit : klBitsDyadic 8 1 = 7 := rfl

/-- KL on identical depths collapses regardless of value. -/
theorem kl_collapse_when_equal (a : Nat) :
    klBitsDyadic a a = klBitsDyadic 0 0 := by
  show a - a = 0 - 0
  rw [Nat.sub_self, Nat.sub_self]

end E213.Lib.Math.Information.KLDivergence
