import E213.Lib.Math.Combinatorics.Derangements
import E213.Lib.Math.Combinatorics.SurjectionCount
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.NatRing213

/-!
# Derangement inclusion–exclusion closed form (∅-axiom)

`dIE n := Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)!` over `Int`, and the headline

  ★★★ **`derange_eq_inclusion_exclusion`** : `(derange n : ℤ) = dIE n`
      i.e. `!n = Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)!` — the subfactorial as the
      classical inclusion–exclusion alternating sum.

Route: `dIE` satisfies the SAME one-term `±1` recurrence the corpus `derange`
obeys (`derange_one_term` : `D_{n+1} = (n+1)·D_n + (−1)^{n+1}`), so they agree by
induction with the matching base case `dIE 0 = 1 = derange 0`.

The recurrence-match `dIE (n+1) = (n+1)·dIE n + (−1)^{n+1}` is ONE clean step:
split the top term `k=n+1` of `dIE (n+1)` (`C(n+1,n+1)·0! = 1`, weight `(−1)^{n+1}`),
then on the head `k=0..n` rewrite the summand with the **`choose` absorption**
`(n+1−k)·C(n+1,k) = (n+1)·C(n,k)` (`choose_absorb_int`, reused from
`SurjectionCount`) and the factorial step `(n+1−k)! = (n+1−k)·(n−k)!` (`rfl`, since
`(n+1)−k = (n−k)+1` for `k≤n`).  No extra finite-difference machinery needed.

All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.DerangementInclusionExclusion

open E213.Lib.Math.Combinatorics.Derangements (derange derange_one_term)
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.Combinatorics.SurjectionCount
  (choose_absorb_int ofNat_sub_cast sumZ_mul_left sumZ_congr)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_self)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
  (sumZ sumZ_zero sumZ_succ powNegOne_succ)
open E213.Meta.Int213.PolyIntM (powInt powInt_add one_mulZ mul_zeroZ)

/-- The derangement inclusion–exclusion sum
    `dIE n = Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)!` over `Int`. -/
def dIE (n : Nat) : Int :=
  sumZ (n + 1) (fun k => powInt (-1 : Int) k * (choose n k : Int) * (fact (n - k) : Int))

/-! ## Concrete values (closed numeric `decide`) -/

theorem dIE_0 : dIE 0 = 1 := by decide
theorem dIE_1 : dIE 1 = 0 := by decide
theorem dIE_2 : dIE 2 = 1 := by decide
theorem dIE_3 : dIE 3 = 2 := by decide
theorem dIE_4 : dIE 4 = 9 := by decide
theorem dIE_5 : dIE 5 = 44 := by decide

/-! ## The recurrence-match -/

/-- The per-summand rewrite (for `k ≤ n`): the `dIE (n+1)` head summand equals
    `(n+1)` times the corresponding `dIE n` summand.

    `(−1)^k · C(n+1,k) · (n+1−k)!  =  (n+1) · ((−1)^k · C(n,k) · (n−k)!)`.

    Via `(n+1−k)! = (n+1−k)·(n−k)!` (`rfl` since `(n+1)−k = (n−k)+1`) and the
    absorption `(n+1−k)·C(n+1,k) = (n+1)·C(n,k)` (`choose_absorb_int`). -/
theorem dIE_head_summand (n k : Nat) (hk : k ≤ n) :
    powInt (-1 : Int) k * (choose (n + 1) k : Int) * (fact ((n + 1) - k) : Int)
      = ((n : Int) + 1)
        * (powInt (-1 : Int) k * (choose n k : Int) * (fact (n - k) : Int)) := by
  -- `(n+1)−k = (n−k)+1` (Nat), so `fact ((n+1)−k) = ((n+1−k):Int) · fact (n−k)`.
  have hsub : (n + 1) - k = (n - k) + 1 :=
    E213.Meta.Nat.NatRing213.nat_succ_sub hk
  have hfact : (fact ((n + 1) - k) : Int)
             = (((n : Int) + 1) - (k : Int)) * (fact (n - k) : Int) := by
    rw [hsub]
    show ((((n - k) + 1) * fact (n - k) : Nat) : Int)
       = (((n : Int) + 1) - (k : Int)) * (fact (n - k) : Int)
    rw [show ((((n - k) + 1) * fact (n - k) : Nat) : Int)
          = (((n - k) + 1 : Nat) : Int) * (fact (n - k) : Int) from rfl]
    -- `((n−k)+1 : Int) = (n+1) − k` for `k ≤ n`
    rw [show (((n - k) + 1 : Nat) : Int) = ((n : Int) + 1) - (k : Int) from by
          rw [show (((n - k) + 1 : Nat) : Int) = (((n - k) : Nat) : Int) + 1 from rfl,
              ofNat_sub_cast hk]
          ring_intZ]
  rw [hfact]
  -- Reassociate to expose `(n+1−k)·C(n+1,k)`, apply the absorption.
  have habs := choose_absorb_int n k hk
  rw [show powInt (-1 : Int) k * (choose (n + 1) k : Int)
           * ((((n : Int) + 1) - (k : Int)) * (fact (n - k) : Int))
         = powInt (-1 : Int) k
           * ((((n : Int) + 1) - (k : Int)) * (choose (n + 1) k : Int))
           * (fact (n - k) : Int) from by ring_intZ]
  rw [habs]
  -- `(−1)^k · ((n+1)·C(n,k)) · (n−k)! = (n+1) · ((−1)^k · C(n,k) · (n−k)!)`.
  ring_intZ

/-- ★★ **The one-term `±1` recurrence for `dIE`** — the SAME recurrence the corpus
    `derange` obeys (`derange_one_term`):
    `dIE (n+1) = ((n:ℤ)+1)·dIE n + (−1)^{n+1}`. -/
theorem dIE_one_term (n : Nat) :
    dIE (n + 1) = ((n : Int) + 1) * dIE n + powInt (-1 : Int) (n + 1) := by
  show sumZ (n + 2)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * (fact ((n + 1) - k) : Int))
     = ((n : Int) + 1) * dIE n + powInt (-1 : Int) (n + 1)
  -- Split off the top term `k = n+1`.
  rw [sumZ_succ (n + 1)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * (fact ((n + 1) - k) : Int))]
  -- Top term: `(−1)^{n+1}·C(n+1,n+1)·0! = (−1)^{n+1}`.
  have htop : powInt (-1 : Int) (n + 1) * (choose (n + 1) (n + 1) : Int)
              * (fact ((n + 1) - (n + 1)) : Int) = powInt (-1 : Int) (n + 1) := by
    rw [Nat.sub_self, show fact 0 = 1 from rfl, choose_self (n + 1),
        show ((1 : Nat) : Int) = (1 : Int) from rfl]
    rw [show powInt (-1 : Int) (n + 1) * (1 : Int) * (1 : Int)
          = powInt (-1 : Int) (n + 1) from by ring_intZ]
  -- Rewrite the head sum summandwise into `(n+1) · (dIE n summand)`.
  rw [sumZ_congr (n + 1)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * (fact ((n + 1) - k) : Int))
        (fun k => ((n : Int) + 1)
                  * (powInt (-1 : Int) k * (choose n k : Int) * (fact (n - k) : Int)))
        (fun k hk => dIE_head_summand n k (Nat.le_of_lt_succ hk))]
  -- Pull the scalar `(n+1)` out: head sum = `(n+1) · dIE n`.
  rw [← sumZ_mul_left ((n : Int) + 1) (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n k : Int) * (fact (n - k) : Int))]
  show ((n : Int) + 1) * dIE n
       + powInt (-1 : Int) (n + 1) * (choose (n + 1) (n + 1) : Int)
         * (fact ((n + 1) - (n + 1)) : Int)
     = ((n : Int) + 1) * dIE n + powInt (-1 : Int) (n + 1)
  rw [htop]

/-! ## The closed form -/

/-- ★★★ **Derangement inclusion–exclusion closed form**:
    `(derange n : ℤ) = Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)!`.

    `dIE` and the corpus `derange` satisfy the identical one-term `±1` recurrence
    (`dIE_one_term` ≡ `derange_one_term`) with the matching base case
    `dIE 0 = 1 = derange 0`, hence agree for all `n` by induction. -/
theorem derange_eq_inclusion_exclusion : ∀ n : Nat, (derange n : Int) = dIE n
  | 0 => by decide
  | n + 1 => by
      rw [dIE_one_term n, ← derange_eq_inclusion_exclusion n, derange_one_term n]

/-- Smoke restatement at `n = 5`: `!5 = 44 = Σ_{k=0}^{5} (−1)^k C(5,k)(5−k)!`. -/
theorem derange_eq_inclusion_exclusion_smoke : (derange 5 : Int) = dIE 5 := by decide

end E213.Lib.Math.Combinatorics.DerangementInclusionExclusion
