import E213.Lib.Math.Combinatorics.SurjectionCount
import E213.Lib.Math.Combinatorics.Stirling

/-!
# Stirling-2nd-kind explicit formula: `surj m n = n! · S(m,n)` (∅-axiom)

`Σ_{k=0}^{n} (−1)^k C(n,k)(n−k)^m = n! · S(m,n)` — the number of surjections
[m]↠[n] equals `n!` times the number of partitions of [m] into n blocks.
-/

namespace E213.Lib.Math.Combinatorics.StirlingExplicit

open E213.Lib.Math.Combinatorics.SurjectionCount
  (surj A Δ sumZ_split_first sumZ_mul_left sumZ_congr A_congr
   surj_zero_of_lt surj_diag surj_base_col choose_absorb_int)
open E213.Lib.Math.Combinatorics.Stirling (stirling2 stirling2_zero_above)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt
   choose_succ_mul)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
  (sumZ sumZ_zero sumZ_succ powNegOne_succ)
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Meta.Int213.PolyIntM (powInt powInt_add one_mulZ mul_zeroZ)

/-! ## The surjection recurrence `surj (m+1) (n+1) = (n+1)·surj m (n+1) + (n+1)·surj m n` -/

/-- `surj m n` unfolded to its `sumZ` form. -/
theorem surj_eq_sumZ (m n : Nat) :
    surj m n
      = sumZ (n + 1)
          (fun k => powInt (-1 : Int) k * (choose n k : Int)
                    * powInt ((n : Int) - (k : Int)) m) := rfl

/-- The single-summand split:
    `(−1)^k C(n+1,k) (n+1−k)^{m+1}
      = (n+1)·[(−1)^k C(n+1,k) (n+1−k)^m]
        − k·[(−1)^k C(n+1,k) (n+1−k)^m]`. -/
theorem surj_summand_split (m n k : Nat) :
    powInt (-1 : Int) k * (choose (n + 1) k : Int)
      * powInt (((n : Int) + 1) - (k : Int)) (m + 1)
    = ((n : Int) + 1)
        * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
           * powInt (((n : Int) + 1) - (k : Int)) m)
      - (k : Int)
        * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
           * powInt (((n : Int) + 1) - (k : Int)) m) := by
  have hpow : powInt (((n : Int) + 1) - (k : Int)) (m + 1)
            = powInt (((n : Int) + 1) - (k : Int)) m * (((n : Int) + 1) - (k : Int)) := rfl
  rw [hpow]
  generalize powInt (((n : Int) + 1) - (k : Int)) m = P
  generalize powInt (-1 : Int) k = s
  generalize (choose (n + 1) k : Int) = c
  ring_intZ

/-- `Int` sum distributes over pointwise subtraction. -/
theorem sumZ_sub_func : ∀ (n : Nat) (f g : Nat → Int),
    sumZ n (fun k => f k - g k) = sumZ n f - sumZ n g
  | 0, _, _ => by
      show (0 : Int) = 0 - 0
      rw [Int.sub_eq_add_neg, E213.Meta.Int213.PolyIntM.neg_zeroZ,
          E213.Meta.Int213.zero_add]
  | n + 1, f, g => by
      show sumZ n (fun k => f k - g k) + (f n - g n)
         = (sumZ n f + f n) - (sumZ n g + g n)
      rw [sumZ_sub_func n f g]
      generalize sumZ n f = F
      generalize sumZ n g = G
      ring_intZ

/-- `SA = surj m (n+1)`: the offset-`(n+1)` body equals the surj body at `n+1`. -/
theorem SA_eq (m n : Nat) :
    sumZ (n + 2)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) m)
      = surj m (n + 1) := by
  rw [surj_eq_sumZ m (n + 1)]
  apply sumZ_congr
  intro k _
  show powInt (-1 : Int) k * (choose (n + 1) k : Int)
        * powInt (((n : Int) + 1) - (k : Int)) m
     = powInt (-1 : Int) k * (choose (n + 1) k : Int)
        * powInt (((n + 1 : Nat) : Int) - (k : Int)) m
  rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl]

/-- `SB = −(n+1)·surj m n`: the `k`-weighted sum reindexes (via `k·C(n+1,k) =
    (n+1)·C(n,k−1)`, i.e. `choose_succ_mul`) to `−(n+1)·surj m n`. -/
theorem SB_eq (m n : Nat) :
    sumZ (n + 2)
        (fun k => (k : Int)
                  * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
                     * powInt (((n : Int) + 1) - (k : Int)) m))
      = - (((n : Int) + 1) * surj m n) := by
  -- peel the k = 0 term (vanishes), reindex the tail by choose_succ_mul
  rw [sumZ_split_first (n + 1)
        (fun k => (k : Int)
                  * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
                     * powInt (((n : Int) + 1) - (k : Int)) m))]
  -- head term: k = 0 ⇒ factor (0 : Int) ⇒ 0
  rw [show ((0 : Nat) : Int)
          * (powInt (-1 : Int) 0 * (choose (n + 1) 0 : Int)
             * powInt (((n : Int) + 1) - ((0 : Nat) : Int)) m) = 0 from by
        rw [show ((0 : Nat) : Int) = (0 : Int) from rfl,
            E213.Meta.Int213.zero_mul]]
  rw [E213.Meta.Int213.zero_add]
  -- tail: summand at k = (k+1)·[...] rewrites to −(n+1)·[(−1)^k C(n,k) (n−k)^m]
  rw [sumZ_congr (n + 1)
        (fun k => ((k + 1 : Nat) : Int)
                  * (powInt (-1 : Int) (k + 1) * (choose (n + 1) (k + 1) : Int)
                     * powInt (((n : Int) + 1) - ((k + 1 : Nat) : Int)) m))
        (fun k => - (((n : Int) + 1)
                  * (powInt (-1 : Int) k * (choose n k : Int)
                     * powInt ((n : Int) - (k : Int)) m)))
        (fun k _ => by
          show ((k + 1 : Nat) : Int)
                  * (powInt (-1 : Int) (k + 1) * (choose (n + 1) (k + 1) : Int)
                     * powInt (((n : Int) + 1) - ((k + 1 : Nat) : Int)) m)
             = - (((n : Int) + 1)
                  * (powInt (-1 : Int) k * (choose n k : Int)
                     * powInt ((n : Int) - (k : Int)) m))
          -- (k+1)·C(n+1,k+1) = (n+1)·C(n,k)  via choose_succ_mul (cast to Int)
          have habs : ((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int)
                    = ((n : Int) + 1) * (choose n k : Int) := by
            have hN := choose_succ_mul n k
            have hc : (((k + 1) * choose (n + 1) (k + 1) : Nat) : Int)
                    = (((n + 1) * choose n k : Nat) : Int) := by rw [hN]
            rw [show (((k + 1) * choose (n + 1) (k + 1) : Nat) : Int)
                  = ((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int) from rfl,
                show (((n + 1) * choose n k : Nat) : Int)
                  = ((n + 1 : Nat) : Int) * (choose n k : Int) from rfl,
                show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl] at hc
            exact hc
          -- powInt (-1) (k+1) = - powInt (-1) k
          rw [powNegOne_succ k]
          -- (n+1) - (k+1) = n - k  inside the base
          rw [show (((n : Int) + 1) - ((k + 1 : Nat) : Int)) = (n : Int) - (k : Int) from by
                rw [show ((k + 1 : Nat) : Int) = (k : Int) + 1 from rfl]; ring_intZ]
          -- regroup: (k+1)·((−p)·C(n+1,k+1)·Q) = −((k+1)·C(n+1,k+1))·p·Q
          --        = −((n+1)·C(n,k))·p·Q = −((n+1)·(p·C(n,k)·Q))
          generalize powInt ((n : Int) - (k : Int)) m = Q
          generalize powInt (-1 : Int) k = p
          rw [show ((k + 1 : Nat) : Int)
                  * (- p * (choose (n + 1) (k + 1) : Int) * Q)
                = - (((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int)) * (p * Q) from by
                ring_intZ]
          rw [habs]
          show - (((n : Int) + 1) * (choose n k : Int)) * (p * Q)
             = - (((n : Int) + 1) * (p * (choose n k : Int) * Q))
          ring_intZ)]
  -- now: sumZ (n+1) (fun k => −((n+1)·body)) = −((n+1)·surj m n)
  rw [sumZ_congr (n + 1)
        (fun k => - (((n : Int) + 1)
                  * (powInt (-1 : Int) k * (choose n k : Int)
                     * powInt ((n : Int) - (k : Int)) m)))
        (fun k => (- ((n : Int) + 1))
                  * (powInt (-1 : Int) k * (choose n k : Int)
                     * powInt ((n : Int) - (k : Int)) m))
        (fun k _ => by
          show - (((n : Int) + 1)
                  * (powInt (-1 : Int) k * (choose n k : Int)
                     * powInt ((n : Int) - (k : Int)) m))
             = (- ((n : Int) + 1))
                  * (powInt (-1 : Int) k * (choose n k : Int)
                     * powInt ((n : Int) - (k : Int)) m)
          generalize powInt (-1 : Int) k * (choose n k : Int)
                     * powInt ((n : Int) - (k : Int)) m = B
          exact (E213.Meta.Int213.neg_mul ((n : Int) + 1) B).symm)]
  rw [← sumZ_mul_left (- ((n : Int) + 1)) (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n k : Int)
                  * powInt ((n : Int) - (k : Int)) m)]
  rw [show sumZ (n + 1)
            (fun k => powInt (-1 : Int) k * (choose n k : Int)
                      * powInt ((n : Int) - (k : Int)) m)
        = surj m n from (surj_eq_sumZ m n).symm]
  generalize surj m n = S
  ring_intZ

/-- ★★★ **Surjection recurrence**
    `surj (m+1) (n+1) = (n+1)·surj m (n+1) + (n+1)·surj m n`. -/
theorem surj_rec (m n : Nat) :
    surj (m + 1) (n + 1)
      = ((n : Int) + 1) * surj m (n + 1) + ((n : Int) + 1) * surj m n := by
  show A (n + 1) (fun k => powInt (((n + 1 : Nat) : Int) - (k : Int)) (m + 1))
     = ((n : Int) + 1) * surj m (n + 1) + ((n : Int) + 1) * surj m n
  show sumZ (n + 2)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * powInt (((n + 1 : Nat) : Int) - (k : Int)) (m + 1))
     = ((n : Int) + 1) * surj m (n + 1) + ((n : Int) + 1) * surj m n
  rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl]
  -- split each summand
  rw [sumZ_congr (n + 2)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) (m + 1))
        (fun k => ((n : Int) + 1)
                    * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
                       * powInt (((n : Int) + 1) - (k : Int)) m)
                  - (k : Int)
                    * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
                       * powInt (((n : Int) + 1) - (k : Int)) m))
        (fun k _ => surj_summand_split m n k)]
  rw [sumZ_sub_func (n + 2)
        (fun k => ((n : Int) + 1)
                    * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
                       * powInt (((n : Int) + 1) - (k : Int)) m))
        (fun k => (k : Int)
                    * (powInt (-1 : Int) k * (choose (n + 1) k : Int)
                       * powInt (((n : Int) + 1) - (k : Int)) m))]
  -- first sum = (n+1)·SA = (n+1)·surj m (n+1)
  rw [← sumZ_mul_left ((n : Int) + 1) (n + 2)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) m)]
  rw [SA_eq m n]
  -- second sum = SB = −(n+1)·surj m n
  rw [SB_eq m n]
  generalize surj m (n + 1) = X
  generalize surj m n = Y
  ring_intZ

/-! ## The explicit formula `surj m n = n! · S(m,n)` -/

/-- Base case `m = 0`: `surj 0 n = n! · S(0,n)` (`= n!·[n=0]`). -/
theorem surj_eq_base : ∀ n, surj 0 n = (fact n : Int) * (stirling2 0 n : Int)
  | 0 => by decide
  | k + 1 => by
      rw [surj_zero_of_lt (Nat.succ_pos k)]
      show (0 : Int) = (fact (k + 1) : Int) * (stirling2 0 (k + 1) : Int)
      rw [show stirling2 0 (k + 1) = 0 from rfl,
          show ((0 : Nat) : Int) = (0 : Int) from rfl, mul_zeroZ]

/-- ★★★ **Stirling explicit formula** `surj m n = n! · S(m,n)`:
    `Σ_{k=0}^{n} (−1)^k C(n,k)(n−k)^m = n! · S(m,n)` — surjections [m]↠[n]
    count = `n!` × set-partitions of [m] into n blocks.  Induction on `m`,
    matching the `surj` recurrence (`surj_rec`) against the Stirling
    recurrence `S(m+1,n+1) = (n+1)·S(m,n+1) + S(m,n)`. -/
theorem surj_eq_fact_mul_stirling :
    ∀ m n, surj m n = (fact n : Int) * (stirling2 m n : Int)
  | 0,     n     => surj_eq_base n
  | m + 1, 0     => by
      have h := (surj_base_col).2 m
      rw [h]
      show (0 : Int) = (fact 0 : Int) * (stirling2 (m + 1) 0 : Int)
      rw [show stirling2 (m + 1) 0 = 0 from rfl,
          show ((0 : Nat) : Int) = (0 : Int) from rfl, mul_zeroZ]
  | m + 1, k + 1 => by
      rw [surj_rec m k,
          surj_eq_fact_mul_stirling m (k + 1),
          surj_eq_fact_mul_stirling m k]
      -- goal:
      --   (k+1)·(fact(k+1)·S(m,k+1)) + (k+1)·(fact k·S(m,k))
      -- = fact(k+1)·S(m+1,k+1)
      show ((k : Int) + 1) * ((fact (k + 1) : Int) * (stirling2 m (k + 1) : Int))
            + ((k : Int) + 1) * ((fact k : Int) * (stirling2 m k : Int))
         = (fact (k + 1) : Int) * (stirling2 (m + 1) (k + 1) : Int)
      -- expand S(m+1,k+1) = (k+1)·S(m,k+1) + S(m,k)
      rw [show stirling2 (m + 1) (k + 1)
            = (k + 1) * stirling2 m (k + 1) + stirling2 m k from rfl]
      rw [show ((((k + 1) * stirling2 m (k + 1) + stirling2 m k : Nat)) : Int)
            = (((k : Int) + 1) * (stirling2 m (k + 1) : Int))
              + (stirling2 m k : Int) from by
            rw [show ((((k + 1) * stirling2 m (k + 1) + stirling2 m k : Nat)) : Int)
                  = (((k + 1) * stirling2 m (k + 1) : Nat) : Int)
                    + (stirling2 m k : Int) from rfl,
                show ((((k + 1) * stirling2 m (k + 1) : Nat)) : Int)
                  = ((k + 1 : Nat) : Int) * (stirling2 m (k + 1) : Int) from rfl,
                show ((k + 1 : Nat) : Int) = (k : Int) + 1 from rfl]]
      -- fact(k+1) = (k+1)·fact k
      rw [show (fact (k + 1) : Int) = ((k : Int) + 1) * (fact k : Int) from by
            rw [show (fact (k + 1) : Int) = (((k + 1) * fact k : Nat)) from rfl,
                show ((((k + 1) * fact k : Nat))) = ((k + 1 : Nat) : Int) * (fact k : Int) from rfl,
                show ((k + 1 : Nat) : Int) = (k : Int) + 1 from rfl]]
      generalize (stirling2 m (k + 1) : Int) = A
      generalize (stirling2 m k : Int) = B
      generalize (fact k : Int) = F
      ring_intZ

/-! ## Smoke tests for the target formula (closed numeric) -/

theorem smoke_32 : surj 3 2 = (fact 2 : Int) * (stirling2 3 2 : Int) := by decide
theorem smoke_42 : surj 4 2 = (fact 2 : Int) * (stirling2 4 2 : Int) := by decide
theorem smoke_33 : surj 3 3 = (fact 3 : Int) * (stirling2 3 3 : Int) := by decide
theorem smoke_43 : surj 4 3 = (fact 3 : Int) * (stirling2 4 3 : Int) := by decide
theorem smoke_00 : surj 0 0 = (fact 0 : Int) * (stirling2 0 0 : Int) := by decide

end E213.Lib.Math.Combinatorics.StirlingExplicit
