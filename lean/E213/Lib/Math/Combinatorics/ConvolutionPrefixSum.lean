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


/-- `sumTo m (fun _ => 1) = m` — summing `m` ones. -/
theorem sumTo_ones : ∀ m, sumTo m (fun _ => 1) = m
  | 0     => rfl
  | m + 1 => by show sumTo m (fun _ => 1) + 1 = m + 1; rw [sumTo_ones m]

/-- ★ **`conv ones ones n = n + 1`** — convolving the two constant-`1` sequences counts the
    cuts of `n` (there are `n+1` of them, `length_natSplits`): the generating-function
    `1/(1−x)² = Σ (n+1) xⁿ`.  A prefix-sum of ones. -/
theorem conv_ones_ones (n : Nat) : conv ones ones n = n + 1 := by
  rw [conv_ones_prefixSum]
  exact sumTo_ones (n + 1)


/-- `sumTo` respects pointwise equality (local copy). -/
theorem sumTo_congr {g1 g2 : Nat → Nat} (h : ∀ j, g1 j = g2 j) : ∀ m, sumTo m g1 = sumTo m g2
  | 0     => rfl
  | m + 1 => by show sumTo m g1 + g1 m = sumTo m g2 + g2 m; rw [sumTo_congr h m, h m]

/-- ★ **Iterated integration**: convolving twice with `ones` is the double prefix-sum.
    `conv ones (conv ones f) n = Σ_{m≤n} Σ_{j≤m} f j` — the discrete antiderivative applied
    twice (the `1/(1−x)²` operator), pairing with the second derivative. -/
theorem conv_ones_ones_prefixSum (f : Nat → Nat) (n : Nat) :
    conv ones (conv ones f) n = sumTo (n + 1) (fun m => sumTo (m + 1) f) := by
  rw [conv_ones_prefixSum]
  exact sumTo_congr (fun m => conv_ones_prefixSum f m) (n + 1)

end E213.Lib.Math.Combinatorics.ConvolutionPrefixSum
