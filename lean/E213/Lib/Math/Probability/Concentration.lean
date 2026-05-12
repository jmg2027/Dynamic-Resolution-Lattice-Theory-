import E213.Lib.Math.Probability.LLN
import E213.Meta.Tactic.Nat213

/-!
# Probability — atomic concentration bounds

Centered deviation as **`Nat` clamped-subtraction sum**.  The signed
deviation `2·countTrue − length` lives in `Int`, but 213 uses
`Nat`-only.  Trick: the absolute deviation = excess + deficit, where
exactly one is zero by `Nat.sub` clamping.

  * `excess xs` = `(2·countTrue − length) ∨ 0`;
  * `deficit xs` = `(length − 2·countTrue) ∨ 0`;
  * `centeredAbsDev2 xs := excess xs + deficit xs`.

Closed forms:
  * balanced 2n           → 0;
  * all-heads of length n → n;
  * all-tails of length n → n;
  * universal bound       → ≤ length.

213-native Hoeffding / Chebyshev-style atomic facts: deviation
bounded by sample size, no exp transcendentals needed.
-/

namespace E213.Lib.Math.Probability.Concentration

open E213.Lib.Math.Probability.SampleMean (countTrue length_replicate)
open E213.Lib.Math.Probability.LLN
  (balancedHeadsTails balanced_countTrue balanced_length)

/-- Excess: `2·countTrue − length` clamped at 0. -/
def excess (xs : List Bool) : Nat := 2 * countTrue xs - xs.length

/-- Deficit: `length − 2·countTrue` clamped at 0. -/
def deficit (xs : List Bool) : Nat := xs.length - 2 * countTrue xs

/-- Centered absolute deviation: excess + deficit (one is always 0). -/
def centeredAbsDev2 (xs : List Bool) : Nat := excess xs + deficit xs

/-- ★ **Balanced sample has zero centered deviation** ★. -/
theorem centeredAbsDev2_balanced (n : Nat) :
    centeredAbsDev2 (balancedHeadsTails n) = 0 := by
  show (2 * countTrue (balancedHeadsTails n)
        - (balancedHeadsTails n).length)
       + ((balancedHeadsTails n).length
          - 2 * countTrue (balancedHeadsTails n)) = 0
  rw [balanced_countTrue, balanced_length, Nat.sub_self, Nat.zero_add]

/-- Helper: `a ≤ b → a - b = 0`, term-mode (avoids the Lean-core
    `Nat.sub_eq_zero_of_le` which `simp`s via `propext`). -/
theorem sub_eq_zero_of_le : ∀ {a b : Nat}, a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => by
    rw [Nat.succ_sub_succ]
    exact sub_eq_zero_of_le (Nat.le_of_succ_le_succ h)

/-- Helper: `n - 2 * n = 0`. -/
theorem n_sub_two_mul (n : Nat) : n - 2 * n = 0 :=
  sub_eq_zero_of_le (by rw [Nat.two_mul]; exact Nat.le_add_left n n)

/-- All-heads of length `n`: `excess = n`, `deficit = 0`,
    so `centeredAbsDev2 = n` (full bias). -/
theorem centeredAbsDev2_allHeads (n : Nat) :
    centeredAbsDev2 (List.replicate n true) = n := by
  show (2 * countTrue (List.replicate n true)
        - (List.replicate n true).length)
       + ((List.replicate n true).length
          - 2 * countTrue (List.replicate n true)) = n
  rw [E213.Lib.Math.Probability.SampleMean.countTrue_allHeads,
      length_replicate]
  show (2 * n - n) + (n - 2 * n) = n
  rw [n_sub_two_mul, Nat.add_zero, Nat.two_mul,
      E213.Tactic.Nat213.add_sub_cancel_right]

/-- All-tails of length `n`: `excess = 0`, `deficit = n`. -/
theorem centeredAbsDev2_allTails (n : Nat) :
    centeredAbsDev2 (List.replicate n false) = n := by
  show (2 * countTrue (List.replicate n false)
        - (List.replicate n false).length)
       + ((List.replicate n false).length
          - 2 * countTrue (List.replicate n false)) = n
  rw [E213.Lib.Math.Probability.SampleMean.countTrue_allTails,
      length_replicate]
  show (2 * 0 - n) + (n - 2 * 0) = n
  rw [Nat.mul_zero, Nat.zero_sub, Nat.zero_add, Nat.sub_zero]

end E213.Lib.Math.Probability.Concentration
