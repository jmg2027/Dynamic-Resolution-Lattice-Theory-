import E213.Meta.Nat.Convolution213
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# ConvolutionPrefixSum — `conv` with the constant `1` is the prefix-sum operator

The generating-function identity `1/(1−x) · F = Σ F`: convolving a sequence `f` with the
constant-`1` sequence `ones` accumulates its prefix sums.

> ★★ `conv_ones_prefixSum` : `conv ones f n = sumTo (n+1) f` (`= Σ_{j≤n} f j`).

This is the **integration twin** of the formal derivative `deriv`/Leibniz
(`Convolution213.conv_leibniz`): `conv ones` is the discrete antiderivative on the
generating-function semiring, and the proof is clean because `ones` is constant
(`shiftL ones = ones`), so `conv_peelL` folds the recursion directly into `sumTo`'s.

All zero-axiom.
-/

namespace E213.Lib.Math.Combinatorics.ConvolutionPrefixSum

open E213.Meta.Nat.Convolution213 (conv conv_peelL conv_congr_left shiftL)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-- The constant-`1` generating function. -/
def ones : Nat → Nat := fun _ => 1

/-- ★★ **`conv` with `ones` is the prefix-sum.**  `conv ones f n = Σ_{j≤n} f j = sumTo (n+1) f`.
    The discrete antiderivative; the integration twin of `deriv`/Leibniz. -/
theorem conv_ones_prefixSum (f : Nat → Nat) : ∀ n, conv ones f n = sumTo (n + 1) f
  | 0     => by
      show (1 : Nat) * f 0 = 0 + f 0
      rw [Nat.one_mul, Nat.zero_add]
  | n + 1 => by
      rw [conv_peelL ones f n,
          conv_congr_left (f1 := shiftL ones) (f2 := ones) (g := f) (fun _ => rfl) n,
          conv_ones_prefixSum f n]
      show (1 : Nat) * f (n + 1) + sumTo (n + 1) f = sumTo (n + 1) f + f (n + 1)
      rw [Nat.one_mul, Nat.add_comm]

end E213.Lib.Math.Combinatorics.ConvolutionPrefixSum
