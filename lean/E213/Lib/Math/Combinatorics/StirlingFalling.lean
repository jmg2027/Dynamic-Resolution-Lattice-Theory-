import E213.Lib.Math.Combinatorics.Stirling
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Tactic.NatHelper

/-!
# Stirling-number defining identity `Σ S(n,k)·x^{(k)} = xⁿ` (∅-axiom)

The identity that *defines* the second-kind Stirling numbers: they are the
change-of-basis coefficients from the falling-factorial basis to the monomial
basis.

  ★ `stirling_falling` / `stirling_falling_sum` : `Σ_{k=0}^{n} S(n,k)·x^{(k)} = xⁿ`

where `S(n,k) = stirling2` (corpus) and `x^{(k)}` is the falling factorial
`ff x k = x·(x−1)···(x−k+1)`.  Truncated Nat subtraction matches `S`'s support:
for `x < k`, `ff x k = 0` (a factor `(x−j)` vanishes), exactly where the partition
count contributes nothing.

The engine is the falling-factorial absorption
  `x · ff x k = ff x (k+1) + k · ff x k`
(`x = (x−k) + k` for `k ≤ x`; both sides vanish for `x < k`).  Induction on `n`:
compute `x · S x n` two ways — pull `x` in + absorb (`x_mul_S`), and head-peel +
reindex + the Stirling recurrence `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)`
(`S_succ_eq`, closed by the tail-shift `tail_shift`) — and match, with
`x^{n+1} = x·xⁿ`.  Same Pascal-split/reindex template as `Vandermonde.lean`.
All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.StirlingFalling

open E213.Lib.Math.Combinatorics.Stirling (stirling2 stirling2_zero_above)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr sumTo_mul_left)
open E213.Tactic.NatHelper (add_mul mul_assoc sub_add_cancel)

/-- Falling factorial `ff x k = x·(x−1)···(x−k+1)` (truncated Nat subtraction). -/
def ff (x : Nat) : Nat → Nat
  | 0     => 1
  | k + 1 => ff x k * (x - k)

theorem ff_zero (x : Nat) : ff x 0 = 1 := rfl
theorem ff_succ (x k : Nat) : ff x (k + 1) = ff x k * (x - k) := rfl

/-- For `x < k`, the falling factorial vanishes: the factor `(x − x) = 0` appears
    once `k` overshoots `x`.  By induction on `k`. -/
theorem ff_zero_of_lt : ∀ {x k : Nat}, x < k → ff x k = 0
  | _, 0,     h => absurd h (Nat.not_lt_zero _)
  | x, k + 1, h => by
      show ff x k * (x - k) = 0
      rcases Nat.lt_or_ge x k with hlt | hge
      · rw [ff_zero_of_lt hlt, Nat.zero_mul]
      · have hxk : x = k := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
        rw [hxk, Nat.sub_self, Nat.mul_zero]

/-- ★ **Falling-factorial absorption**: `x · ff x k = ff x (k+1) + k · ff x k`.

    For `k ≤ x`: `x = (x−k) + k`, distribute over `ff x k`, and
    `ff x (k+1) = ff x k · (x−k)`.  For `x < k`: every term is `0`. -/
theorem ff_absorb (x k : Nat) :
    x * ff x k = ff x (k + 1) + k * ff x k := by
  rcases Nat.lt_or_ge k (x + 1) with hle | hgt
  · have hkx : k ≤ x := Nat.le_of_lt_succ hle
    have hx : (x - k) + k = x := sub_add_cancel hkx
    show x * ff x k = ff x k * (x - k) + k * ff x k
    have e1 : x * ff x k = ((x - k) + k) * ff x k :=
      congrArg (fun t => t * ff x k) hx.symm
    rw [e1, add_mul (x - k) k (ff x k), Nat.mul_comm (x - k) (ff x k)]
  · have hxk : x < k := hgt
    have h0 : ff x k = 0 := ff_zero_of_lt hxk
    have h1 : ff x (k + 1) = 0 := ff_zero_of_lt (Nat.lt_succ_of_lt hxk)
    rw [h0, h1, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]

/-! ## The generalized Stirling sum and its inductive step -/

/-- The Stirling sum, generalized so we can induct on `n`. -/
def S (x n : Nat) : Nat := sumTo (n + 1) (fun k => stirling2 n k * ff x k)

/-- `S x 0 = 1` (the only term is `stirling2 0 0 · ff x 0 = 1·1`). -/
theorem S_zero (x : Nat) : S x 0 = 1 := by
  show sumTo 1 (fun k => stirling2 0 k * ff x k) = 1
  show (0 : Nat) + stirling2 0 0 * ff x 0 = 1
  show (0 : Nat) + 1 * 1 = 1
  rfl

/-- `x · S x n` decomposed (pull `x` in, then absorb each term):
    `x · S x n = Σ S(n,k)·ff x (k+1) + Σ S(n,k)·(k·ff x k)`. -/
theorem x_mul_S (x n : Nat) :
    x * S x n
      = sumTo (n + 1) (fun k => stirling2 n k * ff x (k + 1))
        + sumTo (n + 1) (fun k => stirling2 n k * (k * ff x k)) := by
  show x * sumTo (n + 1) (fun k => stirling2 n k * ff x k)
     = sumTo (n + 1) (fun k => stirling2 n k * ff x (k + 1))
       + sumTo (n + 1) (fun k => stirling2 n k * (k * ff x k))
  rw [sumTo_mul_left x (n + 1) (fun k => stirling2 n k * ff x k)]
  rw [sumTo_congr (n + 1)
        (fun k => x * (stirling2 n k * ff x k))
        (fun k => stirling2 n k * ff x (k + 1) + stirling2 n k * (k * ff x k))
        (fun k _ => by
          show x * (stirling2 n k * ff x k)
             = stirling2 n k * ff x (k + 1) + stirling2 n k * (k * ff x k)
          rw [Nat.mul_comm x (stirling2 n k * ff x k),
              mul_assoc (stirling2 n k) (ff x k) x,
              Nat.mul_comm (ff x k) x,
              ff_absorb x k,
              Nat.mul_add (stirling2 n k) (ff x (k + 1)) (k * ff x k)])]
  rw [← sumTo_add_func (n + 1)
        (fun k => stirling2 n k * ff x (k + 1))
        (fun k => stirling2 n k * (k * ff x k))]

/-- `S x (n+1)` head-peeled and tail-reindexed:
    `S x (n+1) = Σ_{k=0}^{n} S(n+1,k+1)·ff x (k+1)` (`k=0` term is `S(n+1,0)·ff x 0 = 0`). -/
theorem S_succ_reindex (x n : Nat) :
    S x (n + 1)
      = sumTo (n + 1) (fun k => stirling2 (n + 1) (k + 1) * ff x (k + 1)) := by
  show sumTo (n + 2) (fun k => stirling2 (n + 1) k * ff x k)
     = sumTo (n + 1) (fun k => stirling2 (n + 1) (k + 1) * ff x (k + 1))
  rw [sumTo_split_first (n + 1) (fun k => stirling2 (n + 1) k * ff x k)]
  show stirling2 (n + 1) 0 * ff x 0
       + sumTo (n + 1) (fun k => stirling2 (n + 1) (k + 1) * ff x (k + 1))
     = sumTo (n + 1) (fun k => stirling2 (n + 1) (k + 1) * ff x (k + 1))
  show (0 : Nat) * ff x 0
       + sumTo (n + 1) (fun k => stirling2 (n + 1) (k + 1) * ff x (k + 1))
     = sumTo (n + 1) (fun k => stirling2 (n + 1) (k + 1) * ff x (k + 1))
  rw [Nat.zero_mul, Nat.zero_add]

/-- Tail-shift: `Σ_{k=0}^{n} S(n,k+1)·((k+1)·ff x (k+1)) = Σ_{k=0}^{n} S(n,k)·(k·ff x k)`.
    RHS peels `k=0` (term `0`), reindexes to shifted index; LHS and the result differ
    only by the top term `S(n,n+1)·(…) = 0` (`stirling2 n (n+1) = 0`, `n < n+1`). -/
theorem tail_shift (x n : Nat) :
    sumTo (n + 1) (fun k => stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))
      = sumTo (n + 1) (fun k => stirling2 n k * (k * ff x k)) := by
  rw [sumTo_split_first n (fun k => stirling2 n k * (k * ff x k))]
  show sumTo (n + 1) (fun k => stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))
     = stirling2 n 0 * (0 * ff x 0)
       + sumTo n (fun k => stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))
  rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
  rw [sumTo_succ n (fun k => stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))]
  show sumTo n (fun k => stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))
       + stirling2 n (n + 1) * ((n + 1) * ff x (n + 1))
     = sumTo n (fun k => stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))
  rw [stirling2_zero_above (Nat.lt_succ_self n), Nat.zero_mul, Nat.add_zero]

/-- ★ `S x (n+1)` via the Stirling recurrence — matches `x_mul_S` term-for-term:
    `S x (n+1) = Σ S(n,k)·ff x (k+1) + Σ S(n,k)·(k·ff x k)`. -/
theorem S_succ_eq (x n : Nat) :
    S x (n + 1)
      = sumTo (n + 1) (fun k => stirling2 n k * ff x (k + 1))
        + sumTo (n + 1) (fun k => stirling2 n k * (k * ff x k)) := by
  rw [S_succ_reindex x n]
  rw [sumTo_congr (n + 1)
        (fun k => stirling2 (n + 1) (k + 1) * ff x (k + 1))
        (fun k => stirling2 n k * ff x (k + 1)
                  + stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))
        (fun k _ => by
          show stirling2 (n + 1) (k + 1) * ff x (k + 1)
             = stirling2 n k * ff x (k + 1)
               + stirling2 n (k + 1) * ((k + 1) * ff x (k + 1))
          show ((k + 1) * stirling2 n (k + 1) + stirling2 n k) * ff x (k + 1)
             = stirling2 n k * ff x (k + 1)
               + stirling2 n (k + 1) * ((k + 1) * ff x (k + 1))
          rw [add_mul ((k + 1) * stirling2 n (k + 1)) (stirling2 n k) (ff x (k + 1))]
          rw [Nat.add_comm ((k + 1) * stirling2 n (k + 1) * ff x (k + 1))
                (stirling2 n k * ff x (k + 1))]
          rw [mul_assoc (k + 1) (stirling2 n (k + 1)) (ff x (k + 1)),
              Nat.mul_comm (k + 1) (stirling2 n (k + 1) * ff x (k + 1)),
              mul_assoc (stirling2 n (k + 1)) (ff x (k + 1)) (k + 1),
              Nat.mul_comm (ff x (k + 1)) (k + 1)])]
  rw [← sumTo_add_func (n + 1)
        (fun k => stirling2 n k * ff x (k + 1))
        (fun k => stirling2 n (k + 1) * ((k + 1) * ff x (k + 1)))]
  rw [tail_shift x n]

/-- ★★★ **Stirling defining identity (second kind)**:
    `Σ_{k=0}^{n} S(n,k) · x^{(k)} = xⁿ`.

    Induction on `n`; the step is `x · S x n = S x (n+1)` (via `x_mul_S` and
    `S_succ_eq`), with `x^{n+1} = x · xⁿ`. -/
theorem stirling_falling (x : Nat) : ∀ n, S x n = x ^ n
  | 0 => by rw [S_zero]; rfl
  | n + 1 => by
      have hstep : x * S x n = S x (n + 1) :=
        (x_mul_S x n).trans (S_succ_eq x n).symm
      show S x (n + 1) = x ^ (n + 1)
      rw [← hstep, stirling_falling x n]
      show x * x ^ n = x ^ n * x
      rw [Nat.mul_comm]

/-- Explicit `sumTo` form of the defining identity (unfolds `S`). -/
theorem stirling_falling_sum (x n : Nat) :
    sumTo (n + 1) (fun k => stirling2 n k * ff x k) = x ^ n :=
  stirling_falling x n

/-- Smoke checks: `n = 2,3,4` at small `x`. -/
theorem stirling_falling_smoke_2 :
    sumTo 3 (fun k => stirling2 2 k * ff 5 k) = 5 ^ 2 := by decide
theorem stirling_falling_smoke_3 :
    sumTo 4 (fun k => stirling2 3 k * ff 4 k) = 4 ^ 3 := by decide
theorem stirling_falling_smoke_4 :
    sumTo 5 (fun k => stirling2 4 k * ff 3 k) = 3 ^ 4 := by decide

end E213.Lib.Math.Combinatorics.StirlingFalling
