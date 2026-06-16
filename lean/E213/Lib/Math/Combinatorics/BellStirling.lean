import E213.Lib.Math.Combinatorics.BellNumbers
import E213.Lib.Math.Combinatorics.Stirling
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.FactorialLcmIdentity
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# Bell–Stirling connection, GENERAL: `B_n = Σ_{k=0}^{n} S(n,k)` (∅-axiom)

The corpus had the Bell–Stirling connection `B_n = Σ_{k=0}^{n} S(n,k)` only as a
finite `decide` table (`BellNumbers.bell_eq_stirling_sum`, n ≤ 5).  This file
proves it for **all** `n`.

Crux is the **Stirling block-conditioning identity**
`S(n+1, k'+1) = Σ_{j=0}^{n} C(n,j) · S(j, k')`
(`stirling2_succ_sum`), derived purely from the simple recurrence
`S(m+1,k)=k·S(m,k)+S(m,k−1)` and Pascal.  Summing over `k` and swapping the order
(Fubini) shows `bellS n := Σ_k S(n,k)` satisfies the SAME binomial recurrence as
`bell`, hence `bellS = bell`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.BellStirling

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr sumTo_mul_left)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_self choose_succ_succ choose_eq_zero_of_lt)
open E213.Lib.Math.Combinatorics.Stirling (stirling2 stirling2_zero_above)
open E213.Lib.Math.Combinatorics.BellNumbers (bell bell_succ bell_zero)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_fubini sumTo_extend_vanish)
open E213.Tactic.NatHelper (add_mul)

/-! ## Abbreviations: the row-conditioned sum `R` and its shifted twin `T` -/

/-- `R n k' = Σ_{j=0}^{n} C(n,j) · S(j, k')`. -/
abbrev R (n k' : Nat) : Nat := sumTo (n + 1) (fun j => choose n j * stirling2 j k')

/-- `T n k' = Σ_{i=0}^{n} C(n,i) · S(i+1, k')` (the row sum with the Stirling index
    shifted up by one). -/
abbrev T (n k' : Nat) : Nat := sumTo (n + 1) (fun i => choose n i * stirling2 (i + 1) k')

/-! ## `sumTo (n+1) (fun _ => 0) = 0` -/

theorem sumTo_const_zero : ∀ n, sumTo n (fun _ => (0 : Nat)) = 0
  | 0 => rfl
  | p + 1 => by rw [sumTo_succ, sumTo_const_zero p]

/-! ## Pascal recurrence for `R`: `R (n+1) k' = R n k' + T n k'` -/

/-- Head-split of `R`: `R n k' = C(n,0)·S(0,k') + Σ_{i<n} C(n,i+1)·S(i+1,k')`
    (= `S(0,k') + Σ_{i<n} C(n,i+1)·S(i+1,k')`). -/
theorem R_split_head (n k' : Nat) :
    R n k'
      = stirling2 0 k'
        + sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k') := by
  show sumTo (n + 1) (fun j => choose n j * stirling2 j k')
     = stirling2 0 k'
       + sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k')
  rw [sumTo_split_first n (fun j => choose n j * stirling2 j k')]
  show choose n 0 * stirling2 0 k'
       + sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k')
     = stirling2 0 k'
       + sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k')
  rw [choose_zero_right, Nat.one_mul]

/-- ★ Pascal recurrence for `R`: `R (n+1) k' = R n k' + T n k'`.
    Pure Pascal split + reindex (no induction on Stirling). -/
theorem R_rec (n k' : Nat) : R (n + 1) k' = R n k' + T n k' := by
  show sumTo (n + 2) (fun j => choose (n + 1) j * stirling2 j k')
     = R n k' + T n k'
  rw [sumTo_split_first (n + 1) (fun j => choose (n + 1) j * stirling2 j k')]
  show choose (n + 1) 0 * stirling2 0 k'
       + sumTo (n + 1) (fun i => choose (n + 1) (i + 1) * stirling2 (i + 1) k')
     = R n k' + T n k'
  rw [choose_zero_right, Nat.one_mul]
  -- expand C(n+1,i+1) = C(n,i) + C(n,i+1) inside the tail
  rw [sumTo_congr (n + 1)
        (fun i => choose (n + 1) (i + 1) * stirling2 (i + 1) k')
        (fun i => choose n i * stirling2 (i + 1) k'
                  + choose n (i + 1) * stirling2 (i + 1) k')
        (fun i _ => by
          show choose (n + 1) (i + 1) * stirling2 (i + 1) k'
             = choose n i * stirling2 (i + 1) k'
               + choose n (i + 1) * stirling2 (i + 1) k'
          rw [choose_succ_succ n i, add_mul])]
  -- split the sum of a sum
  rw [← sumTo_add_func (n + 1)
        (fun i => choose n i * stirling2 (i + 1) k')
        (fun i => choose n (i + 1) * stirling2 (i + 1) k')]
  -- the first summand is exactly T n k'
  show stirling2 0 k'
       + (T n k'
          + sumTo (n + 1) (fun i => choose n (i + 1) * stirling2 (i + 1) k'))
     = R n k' + T n k'
  -- close the (n+1)-tail to the n-tail: the i=n term has factor C(n,n+1) = 0
  have htail :
      sumTo (n + 1) (fun i => choose n (i + 1) * stirling2 (i + 1) k')
        = sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k') := by
    show sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k')
          + choose n (n + 1) * stirling2 (n + 1) k'
       = sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k')
    rw [choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n), Nat.zero_mul,
        Nat.add_zero]
  rw [htail, R_split_head n k']
  -- goal: S(0,k') + (T + tailₙ) = (S(0,k') + tailₙ) + T
  generalize sumTo n (fun i => choose n (i + 1) * stirling2 (i + 1) k') = tn
  generalize T n k' = t
  generalize stirling2 0 k' = s0
  ring_nat

/-! ## `T n (m+1) = (m+1)·R n (m+1) + R n m` (via the simple Stirling recurrence) -/

/-- `T n (m+1) = (m+1)·R n (m+1) + R n m`.  Each `S(i+1, m+1)` expands by the simple
    recurrence to `(m+1)·S(i,m+1) + S(i,m)`; the sum splits and `sumTo_mul_left`
    pulls the constant `(m+1)` out. -/
theorem T_succ (n m : Nat) :
    T n (m + 1) = (m + 1) * R n (m + 1) + R n m := by
  show sumTo (n + 1) (fun i => choose n i * stirling2 (i + 1) (m + 1))
     = (m + 1) * R n (m + 1) + R n m
  -- expand S(i+1, m+1) = (m+1)·S(i,m+1) + S(i,m), then distribute over C(n,i)·_
  rw [sumTo_congr (n + 1)
        (fun i => choose n i * stirling2 (i + 1) (m + 1))
        (fun i => (m + 1) * (choose n i * stirling2 i (m + 1))
                  + choose n i * stirling2 i m)
        (fun i _ => by
          show choose n i * stirling2 (i + 1) (m + 1)
             = (m + 1) * (choose n i * stirling2 i (m + 1))
               + choose n i * stirling2 i m
          rw [show stirling2 (i + 1) (m + 1)
                = (m + 1) * stirling2 i (m + 1) + stirling2 i m from rfl]
          generalize stirling2 i (m + 1) = A
          generalize stirling2 i m = B
          generalize choose n i = c
          ring_nat)]
  -- split the sum
  rw [← sumTo_add_func (n + 1)
        (fun i => (m + 1) * (choose n i * stirling2 i (m + 1)))
        (fun i => choose n i * stirling2 i m)]
  -- pull (m+1) out of the first sum; both sums are then R
  rw [sumTo_mul_left (m + 1) (n + 1) (fun i => choose n i * stirling2 i (m + 1))]

/-! ## The block-conditioning identity (the crux) -/

/-- ★★ **Stirling block-conditioning identity**
    `S(n+1, k'+1) = Σ_{j=0}^{n} C(n,j) · S(j, k')`.

    Conditioning on the size `j` of the union of the blocks NOT containing the last
    element: those `j` elements form `k'` blocks (`S(j,k')`), chosen `C(n,j)` ways.
    Induction on `n`; the step uses the simple recurrence
    `S(m+1,k)=k·S(m,k)+S(m,k−1)`, Pascal (`R_rec`), and the IH at two columns
    (via `T_succ`).  ∅-axiom — derived from the recurrence alone. -/
theorem stirling2_succ_sum :
    ∀ n k', stirling2 (n + 1) (k' + 1) = R n k' := by
  intro n
  induction n with
  | zero =>
    intro k'
    -- S(1,k'+1) = (k'+1)·S(0,k'+1) + S(0,k') = S(0,k');  R 0 k' = 0 + C(0,0)·S(0,k')
    show (k' + 1) * stirling2 0 (k' + 1) + stirling2 0 k'
       = 0 + choose 0 0 * stirling2 0 k'
    rw [show stirling2 0 (k' + 1) = 0 from rfl, Nat.mul_zero, Nat.zero_add,
        choose_zero_right, Nat.one_mul, Nat.zero_add]
  | succ n ih =>
    intro k'
    -- LHS: S(n+2, k'+1) = (k'+1)·S(n+1,k'+1) + S(n+1,k')  (simple recurrence)
    show (k' + 1) * stirling2 (n + 1) (k' + 1) + stirling2 (n + 1) k'
       = R (n + 1) k'
    rw [R_rec n k']
    -- R n k' = S(n+1, k'+1)  (IH at column k')
    rw [show R n k' = stirling2 (n + 1) (k' + 1) from (ih k').symm]
    -- remains: (k'+1)·S(n+1,k'+1) + S(n+1,k') = S(n+1,k'+1) + T n k'
    -- evaluate T n k' by cases on k'
    cases k' with
    | zero =>
      -- T n 0 = 0  (S(i+1,0) = 0);  S(n+1,0) = 0
      have hT : T n 0 = 0 := by
        show sumTo (n + 1) (fun i => choose n i * stirling2 (i + 1) 0) = 0
        rw [sumTo_congr (n + 1)
              (fun i => choose n i * stirling2 (i + 1) 0)
              (fun _ => 0)
              (fun i _ => by
                show choose n i * stirling2 (i + 1) 0 = 0
                rw [show stirling2 (i + 1) 0 = 0 from rfl, Nat.mul_zero])]
        exact sumTo_const_zero (n + 1)
      rw [hT]
      show (0 + 1) * stirling2 (n + 1) (0 + 1) + stirling2 (n + 1) 0
         = stirling2 (n + 1) (0 + 1) + 0
      rw [show stirling2 (n + 1) 0 = 0 from rfl, Nat.one_mul, Nat.add_zero,
          Nat.add_zero]
    | succ m =>
      -- T n (m+1) = (m+1)·R n (m+1) + R n m
      rw [T_succ n m]
      -- R n (m+1) = S(n+1, m+2),  R n m = S(n+1, m+1)   (IH again)
      rw [show R n (m + 1) = stirling2 (n + 1) (m + 2) from (ih (m + 1)).symm,
          show R n m = stirling2 (n + 1) (m + 1) from (ih m).symm]
      -- (m+2)·S(n+1,m+2) + S(n+1,m+1)
      --   = S(n+1,m+2) + ((m+1)·S(n+1,m+2) + S(n+1,m+1))
      generalize stirling2 (n + 1) (m + 2) = A
      generalize stirling2 (n + 1) (m + 1) = B
      ring_nat

/-! ## Bell as the diagonal row sum: `bellS` -/

/-- `bellS n = Σ_{k=0}^{n} S(n, k)` — the total partition count of `[n]`. -/
abbrev bellS (n : Nat) : Nat := sumTo (n + 1) (fun k => stirling2 n k)

theorem bellS_zero : bellS 0 = 1 := rfl

/-! ## `bellS` satisfies the binomial recurrence -/

/-- ★ `bellS (n+1) = Σ_{j=0}^{n} C(n,j)·bellS j` — `bellS` satisfies the SAME
    binomial recurrence as `bell`.

    `Σ_k S(n+1,k) = S(n+1,0) + Σ_{k} S(n+1,k'+1)`; the head vanishes, and each
    `S(n+1,k'+1) = Σ_j C(n,j)·S(j,k')` (block-conditioning).  Swapping the order
    of summation (Fubini) gives `Σ_j C(n,j)·Σ_{k'} S(j,k') = Σ_j C(n,j)·bellS j`. -/
theorem bellS_succ (n : Nat) :
    bellS (n + 1) = sumTo (n + 1) (fun j => choose n j * bellS j) := by
  -- LHS: Σ_{k<n+2} S(n+1,k) = S(n+1,0) + Σ_{k'<n+1} S(n+1, k'+1)
  show sumTo (n + 2) (fun k => stirling2 (n + 1) k)
     = sumTo (n + 1) (fun j => choose n j * bellS j)
  rw [sumTo_split_first (n + 1) (fun k => stirling2 (n + 1) k)]
  rw [show stirling2 (n + 1) 0 = 0 from rfl, Nat.zero_add]
  -- each S(n+1,k'+1) = R n k' = Σ_{j<n+1} C(n,j)·S(j,k')
  rw [sumTo_congr (n + 1)
        (fun k => stirling2 (n + 1) (k + 1))
        (fun k => sumTo (n + 1) (fun j => choose n j * stirling2 j k))
        (fun k _ => stirling2_succ_sum n k)]
  -- now Σ_{k<n+1} Σ_{j<n+1} C(n,j)·S(j,k)  — Fubini swap k ↔ j
  rw [sumTo_fubini (fun k j => choose n j * stirling2 j k) (n + 1) (n + 1)]
  -- = Σ_{j<n+1} Σ_{k<n+1} C(n,j)·S(j,k) = Σ_{j<n+1} C(n,j)·Σ_{k<n+1} S(j,k)
  refine sumTo_congr (n + 1) _ _ (fun j hj => ?_)
  show sumTo (n + 1) (fun k => choose n j * stirling2 j k)
     = choose n j * bellS j
  rw [← sumTo_mul_left (choose n j) (n + 1) (fun k => stirling2 j k)]
  -- bellS j sums over k<j+1; extend to k<n+1 (extra terms vanish: S(j,k)=0 for k>j)
  show choose n j * sumTo (n + 1) (fun k => stirling2 j k)
     = choose n j * sumTo (j + 1) (fun k => stirling2 j k)
  have hjn : j + 1 ≤ n + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ hj)
  have hext : sumTo (j + 1) (fun k => stirling2 j k)
            = sumTo (n + 1) (fun k => stirling2 j k) :=
    sumTo_extend_vanish
      (fun e he => stirling2_zero_above (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) he))
      (n + 1) hjn
  rw [hext]

/-! ## `bellS = bell` by strong induction (same recurrence) -/

/-- ★★★ **General Bell–Stirling connection**: `B_n = Σ_{k=0}^{n} S(n,k)` for ALL `n`.

    `bellS` and `bell` both start at `1` and obey the SAME binomial recurrence
    (`bellS_succ` matches `bell_succ`), so they agree everywhere (strong induction). -/
theorem bell_eq_stirling_sum_general :
    ∀ n, bell n = sumTo (n + 1) (fun k => stirling2 n k) := by
  -- prove bellS n = bell n by strong induction, then flip
  have key : ∀ n, bellS n = bell n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      match n with
      | 0 => rfl
      | n + 1 =>
        rw [bellS_succ n, bell_succ n]
        refine sumTo_congr (n + 1) _ _ (fun k hk => ?_)
        show choose n k * bellS k = choose n k * bell k
        rw [ih k hk]
  intro n
  exact (key n).symm

/-! ## Concrete smoke checks (closed numeric, ∅-axiom-clean `decide`) -/

/-- `bellS n = bell n` for `n = 0..6`, matching the corpus `bell_table`
    `B_0..B_6 = 1,1,2,5,15,52,203`. -/
theorem bellS_table :
    bellS 0 = 1 ∧ bellS 1 = 1 ∧ bellS 2 = 2 ∧ bellS 3 = 5
    ∧ bellS 4 = 15 ∧ bellS 5 = 52 ∧ bellS 6 = 203 := by decide

/-- Block-conditioning smoke: `S(n+1,k'+1) = Σ_j C(n,j)·S(j,k')` at several entries. -/
theorem stirling2_succ_sum_smoke :
    stirling2 4 3 = R 3 2 ∧ stirling2 5 2 = R 4 1 ∧ stirling2 6 4 = R 5 3 := by
  decide

end E213.Lib.Math.Combinatorics.BellStirling
