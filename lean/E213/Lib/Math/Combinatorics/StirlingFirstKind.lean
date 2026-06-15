import E213.Lib.Math.Combinatorics.Permutations
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Tactic.NatHelper

/-!
# Unsigned Stirling numbers of the first kind — row-sum identity (∅-axiom)

`c(n,k)` counts permutations of `n` elements with exactly `k` cycles.  Summing
over all cycle-counts gives all permutations:

  ★ `stirling1_row_sum : Σ_{k=0}^{n} c(n,k) = n!`

Recurrence (mirrors the corpus `stirling2` style in `Stirling.lean`):
  `c(0,0)=1`, `c(0,k+1)=0`, `c(n+1,0)=0`, `c(n+1,k+1) = n·c(n,k+1) + c(n,k)`.

Proof: induction on `n`.  Peel `k=0` (`c(n+1,0)=0`), reindex the tail with the
recurrence, split into `n·Σ c(n,k+1) + Σ c(n,k)`.  The second is `n!` (IH); the
first is `n·n!` since the reindexed sum equals the full sum once the `c(n,0)=0`
head and the `c(n,n+1)=0` top vanish.  Same head-peel/reindex template as
`StirlingFalling.lean` / `BinomialTheorem.pascal_row_sum_weighted`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.StirlingFirstKind

open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr sumTo_mul_left)

/-- Unsigned Stirling numbers of the first kind, `c(n,k)` — permutations of `n`
    elements with exactly `k` cycles. -/
def stirling1 : Nat → Nat → Nat
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | _ + 1, 0     => 0
  | n + 1, k + 1 => n * stirling1 n (k + 1) + stirling1 n k

/-- `c(m, k) = 0` when `m < k` (a permutation of `m` elements has at most `m`
    cycles).  Mirrors `stirling2_zero_above`. -/
theorem stirling1_zero_above : ∀ {m k : Nat}, m < k → stirling1 m k = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | m + 1, k + 1, h => by
      have hmk : m < k := Nat.lt_of_succ_lt_succ h
      show m * stirling1 m (k + 1) + stirling1 m k = 0
      rw [stirling1_zero_above (Nat.lt_succ_of_lt hmk), stirling1_zero_above hmk,
          Nat.mul_zero, Nat.add_zero]

/-- The reindexed tail sum equals the full row sum, scaled by `n`:
    `n · Σ_{k=0}^{n} c(n,k+1) = n · Σ_{k=0}^{n} c(n,k)`.

    For `n = 0` both sides vanish.  For `n = m+1`: the top term of the tail sum is
    `c(m+1, m+2) = 0` and the head of the full sum is `c(m+1, 0) = 0`, so both
    sums collapse to `Σ_{k=0}^{m} c(m+1, k+1)`. -/
theorem reindex_scaled (n : Nat) :
    n * sumTo (n + 1) (fun k => stirling1 n (k + 1))
      = n * sumTo (n + 1) (fun k => stirling1 n k) := by
  cases n with
  | zero => rw [Nat.zero_mul, Nat.zero_mul]
  | succ m =>
      have htail :
          sumTo (m + 1 + 1) (fun k => stirling1 (m + 1) (k + 1))
            = sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1)) := by
        show sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1))
               + stirling1 (m + 1) (m + 1 + 1)
             = sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1))
        rw [stirling1_zero_above (Nat.lt_succ_self (m + 1)), Nat.add_zero]
      have hfull :
          sumTo (m + 1 + 1) (fun k => stirling1 (m + 1) k)
            = sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1)) := by
        rw [sumTo_split_first (m + 1) (fun k => stirling1 (m + 1) k)]
        show stirling1 (m + 1) 0
               + sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1))
             = sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1))
        show (0 : Nat) + sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1))
             = sumTo (m + 1) (fun k => stirling1 (m + 1) (k + 1))
        rw [Nat.zero_add]
      exact congrArg (fun s => (m + 1) * s) (htail.trans hfull.symm)

/-- ★★★ **Unsigned first-kind Stirling row sum**:
    `Σ_{k=0}^{n} c(n,k) = n!`.

    Induction on `n`.  Step: peel the `k=0` head (`c(n+1,0)=0`), reindex with the
    recurrence `c(n+1,k+1) = n·c(n,k+1) + c(n,k)`, split into
    `n·Σ c(n,k+1) + Σ c(n,k)`.  `reindex_scaled` turns the first into `n·n!`, the
    IH gives the second `= n!`, and `n! + n·n! = (n+1)·n! = (n+1)!`. -/
theorem stirling1_row_sum : ∀ n, sumTo (n + 1) (fun k => stirling1 n k) = fact n
  | 0 => by
      show (0 : Nat) + stirling1 0 0 = fact 0
      show (0 : Nat) + 1 = 1
      rfl
  | n + 1 => by
      rw [sumTo_split_first (n + 1) (fun k => stirling1 (n + 1) k)]
      show stirling1 (n + 1) 0
             + sumTo (n + 1) (fun k => stirling1 (n + 1) (k + 1))
           = fact (n + 1)
      show (0 : Nat) + sumTo (n + 1) (fun k => stirling1 (n + 1) (k + 1))
           = fact (n + 1)
      rw [Nat.zero_add]
      rw [sumTo_congr (n + 1)
            (fun k => stirling1 (n + 1) (k + 1))
            (fun k => n * stirling1 n (k + 1) + stirling1 n k)
            (fun k _ => rfl)]
      rw [← sumTo_add_func (n + 1)
            (fun k => n * stirling1 n (k + 1))
            (fun k => stirling1 n k)]
      rw [← sumTo_mul_left n (n + 1) (fun k => stirling1 n (k + 1))]
      rw [reindex_scaled n]
      rw [stirling1_row_sum n]
      show n * fact n + fact n = (n + 1) * fact n
      rw [E213.Tactic.NatHelper.add_mul n 1 (fact n), Nat.one_mul]

/-- Smoke: `Σ_{k=0}^{4} c(4,k) = 6+11+6+1 = 24 = 4!`. -/
theorem stirling1_row_sum_smoke :
    sumTo 5 (fun k => stirling1 4 k) = fact 4 := by decide

end E213.Lib.Math.Combinatorics.StirlingFirstKind
