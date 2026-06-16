import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Tactic.NatHelper

/-!
# Vandermonde's identity `Σ C(m,k)·C(n,r−k) = C(m+n,r)` (∅-axiom)

The general convolution of two binomial rows — the binomial-cluster analogue of
the Fibonacci–binomial convolution (`FibBinomialConvolution`).

  ★ `vandermonde` : `Σ_{k=0}^{r} C(m,k)·C(n,r−k) = C(m+n, r)`.
  ★ `sum_choose_sq` : `Σ_{k=0}^{n} C(n,k)² = C(2n, n)` (central-binomial corollary,
    set `m=n, r=n` and use `C(n,n−k)=C(n,k)`).

Proof: generalize to `V m n r = Σ_{k=0}^{r} C(m,k)·C(n,r−k)`, induct on `m` via the
key recurrence `V(m+1) n (r+1) = V m n (r+1) + V m n r` (Pascal-split the head-peeled
tail with `sumTo_add_func`, reindexing truncation-free at `r+1` so `(r+1)−(k+1)=r−k`).
Base `m=0` collapses by `choose 0 (k+1)=0`.  Same Pascal-split/reindex template as
`FibBinomialConvolution`; the Pascal `add_mul` step uses the propext-safe
`E213.Tactic.NatHelper.add_mul` twin (`Nat.add_mul` leaks `propext`).  All ∅-axiom.

Only the `C(a+b,2)` special case (`Combinatorics/Binomial.lean` "Vandermonde-2") existed.
-/

namespace E213.Lib.Math.Combinatorics.Vandermonde

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_zero_succ choose_succ_succ
   choose_eq_zero_of_lt choose_self choose_symm_sum)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
  (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr)
open E213.Tactic.NatHelper (add_mul)

/-- Vandermonde convolution `V m n r = Σ_{k=0}^{r} C(m,k)·C(n, r-k)`. -/
def V (m n r : Nat) : Nat := sumTo (r + 1) (fun k => choose m k * choose n (r - k))

/-- `sumTo n (fun _ => 0) = 0`. -/
theorem sumTo_const_zero : ∀ n, sumTo n (fun _ => (0 : Nat)) = 0
  | 0 => rfl
  | p + 1 => by rw [sumTo_succ, sumTo_const_zero p]

/-- `V 0 n r = C(n, r)`: only the `k=0` term survives (`C(0, k+1) = 0`). -/
theorem V_zero_left (n r : Nat) : V 0 n r = choose n r := by
  show sumTo (r + 1) (fun k => choose 0 k * choose n (r - k)) = choose n r
  rw [sumTo_split_first r (fun k => choose 0 k * choose n (r - k))]
  show choose 0 0 * choose n (r - 0)
       + sumTo r (fun k => choose 0 (k + 1) * choose n (r - (k + 1)))
     = choose n r
  rw [choose_zero_right, Nat.one_mul, Nat.sub_zero]
  rw [sumTo_congr r
        (fun k => choose 0 (k + 1) * choose n (r - (k + 1)))
        (fun _ => 0)
        (fun k _ => by
          show choose 0 (k + 1) * choose n (r - (k + 1)) = 0
          rw [choose_zero_succ, Nat.zero_mul])]
  rw [sumTo_const_zero r, Nat.add_zero]

/-- `V (m+1) n 0 = 1`. -/
theorem V_succ_zero (m n : Nat) : V (m + 1) n 0 = 1 := by
  show sumTo 1 (fun k => choose (m + 1) k * choose n (0 - k)) = 1
  show (0 : Nat) + choose (m + 1) 0 * choose n (0 - 0) = 1
  rw [choose_zero_right, Nat.one_mul, Nat.sub_zero, choose_zero_right, Nat.zero_add]

/-- Head-split of `V`: `V m n (r+1) = C(n, r+1) + Σ_{k<r+1} C(m,k+1)·C(n, r-k)`. -/
theorem V_split_head (m n r : Nat) :
    V m n (r + 1)
      = choose n (r + 1)
        + sumTo (r + 1) (fun k => choose m (k + 1) * choose n (r - k)) := by
  show sumTo (r + 2) (fun k => choose m k * choose n (r + 1 - k))
     = choose n (r + 1)
       + sumTo (r + 1) (fun k => choose m (k + 1) * choose n (r - k))
  rw [sumTo_split_first (r + 1) (fun k => choose m k * choose n (r + 1 - k))]
  show choose m 0 * choose n (r + 1 - 0)
       + sumTo (r + 1) (fun k => choose m (k + 1) * choose n (r + 1 - (k + 1)))
     = choose n (r + 1)
       + sumTo (r + 1) (fun k => choose m (k + 1) * choose n (r - k))
  rw [choose_zero_right, Nat.one_mul, Nat.sub_zero]
  rw [sumTo_congr (r + 1)
        (fun k => choose m (k + 1) * choose n (r + 1 - (k + 1)))
        (fun k => choose m (k + 1) * choose n (r - k))
        (fun k _ => by
          show choose m (k + 1) * choose n (r + 1 - (k + 1))
             = choose m (k + 1) * choose n (r - k)
          rw [show r + 1 - (k + 1) = r - k from Nat.succ_sub_succ_eq_sub r k])]

/-- ★ Key recurrence: `V (m+1) n (r+1) = V m n (r+1) + V m n r`. -/
theorem V_rec (m n r : Nat) : V (m + 1) n (r + 1) = V m n (r + 1) + V m n r := by
  show sumTo (r + 2) (fun k => choose (m + 1) k * choose n (r + 1 - k))
     = V m n (r + 1) + V m n r
  rw [sumTo_split_first (r + 1) (fun k => choose (m + 1) k * choose n (r + 1 - k))]
  show choose (m + 1) 0 * choose n (r + 1 - 0)
       + sumTo (r + 1) (fun k => choose (m + 1) (k + 1) * choose n (r + 1 - (k + 1)))
     = V m n (r + 1) + V m n r
  rw [choose_zero_right, Nat.one_mul, Nat.sub_zero]
  rw [sumTo_congr (r + 1)
        (fun k => choose (m + 1) (k + 1) * choose n (r + 1 - (k + 1)))
        (fun k => choose m k * choose n (r - k) + choose m (k + 1) * choose n (r - k))
        (fun k _ => by
          show choose (m + 1) (k + 1) * choose n (r + 1 - (k + 1))
             = choose m k * choose n (r - k) + choose m (k + 1) * choose n (r - k)
          rw [choose_succ_succ m k, add_mul,
              show r + 1 - (k + 1) = r - k from Nat.succ_sub_succ_eq_sub r k])]
  rw [← sumTo_add_func (r + 1)
        (fun k => choose m k * choose n (r - k))
        (fun k => choose m (k + 1) * choose n (r - k))]
  -- C(n,r+1) + (A + B) = V m n (r+1) + V m n r, where A = V m n r (defeq),
  -- and C(n,r+1) + B = V m n (r+1) (V_split_head).
  have hA : sumTo (r + 1) (fun k => choose m k * choose n (r - k)) = V m n r := rfl
  rw [Nat.add_comm (sumTo (r + 1) (fun k => choose m k * choose n (r - k)))
        (sumTo (r + 1) (fun k => choose m (k + 1) * choose n (r - k)))]
  rw [← Nat.add_assoc (choose n (r + 1))
        (sumTo (r + 1) (fun k => choose m (k + 1) * choose n (r - k)))
        (sumTo (r + 1) (fun k => choose m k * choose n (r - k)))]
  rw [← V_split_head m n r, hA]

/-- ★★★ **Vandermonde's identity**:
    `Σ_{k=0}^{r} C(m,k)·C(n, r-k) = C(m+n, r)`. -/
theorem vandermonde : ∀ (m n r : Nat), V m n r = choose (m + n) r := by
  intro m
  induction m with
  | zero =>
    intro n r
    rw [V_zero_left, Nat.zero_add]
  | succ p ih =>
    intro n r
    cases r with
    | zero =>
      rw [V_succ_zero, choose_zero_right]
    | succ q =>
      rw [V_rec p n q, ih n (q + 1), ih n q]
      show choose (p + n) (q + 1) + choose (p + n) q = choose (p + 1 + n) (q + 1)
      rw [show p + 1 + n = (p + n) + 1 from by rw [Nat.add_right_comm p 1 n],
          choose_succ_succ (p + n) q, Nat.add_comm]

/-- Vandermonde in explicit `sumTo` form. -/
theorem vandermonde_sum (m n r : Nat) :
    sumTo (r + 1) (fun k => choose m k * choose n (r - k)) = choose (m + n) r :=
  vandermonde m n r

/-- ★★ **Central-binomial corollary**:
    `Σ_{k=0}^{n} C(n,k)·C(n,k) = C(2n, n)`.

    Set `m = n`, `r = n` in Vandermonde and use `C(n, n-k) = C(n, k)`. -/
theorem sum_choose_sq (n : Nat) :
    sumTo (n + 1) (fun k => choose n k * choose n k) = choose (2 * n) n := by
  have hsym : sumTo (n + 1) (fun k => choose n k * choose n k)
            = sumTo (n + 1) (fun k => choose n k * choose n (n - k)) := by
    exact sumTo_congr (n + 1)
      (fun k => choose n k * choose n k)
      (fun k => choose n k * choose n (n - k))
      (fun k hk => by
        show choose n k * choose n k = choose n k * choose n (n - k)
        have hkn : k ≤ n := Nat.le_of_lt_succ hk
        have hadd : k + (n - k) = n := E213.Tactic.NatHelper.add_sub_of_le hkn
        rw [choose_symm_sum n k (n - k) hadd])
  rw [hsym]
  rw [show sumTo (n + 1) (fun k => choose n k * choose n (n - k)) = V n n n from rfl]
  rw [vandermonde n n n]
  rw [show n + n = 2 * n from (E213.Tactic.NatHelper.two_mul n).symm]

/-- ★★ **Generalized Vandermonde / Cauchy binomial corollary**:
    `Σ_{k=0}^{m} C(n,k)·C(m,k) = C(n+m, m)` (the general two-parameter form of which
    `sum_choose_sq` is the `n=m` case).  Rewrite `C(m,k)=C(m,m−k)` then apply `vandermonde`. -/
theorem sum_choose_prod (n m : Nat) :
    sumTo (m + 1) (fun k => choose n k * choose m k) = choose (n + m) m := by
  have hsym : sumTo (m + 1) (fun k => choose n k * choose m k)
            = sumTo (m + 1) (fun k => choose n k * choose m (m - k)) := by
    exact sumTo_congr (m + 1)
      (fun k => choose n k * choose m k)
      (fun k => choose n k * choose m (m - k))
      (fun k hk => by
        show choose n k * choose m k = choose n k * choose m (m - k)
        have hkm : k ≤ m := Nat.le_of_lt_succ hk
        have hadd : k + (m - k) = m := E213.Tactic.NatHelper.add_sub_of_le hkm
        rw [choose_symm_sum m k (m - k) hadd])
  rw [hsym]
  rw [show sumTo (m + 1) (fun k => choose n k * choose m (m - k)) = V n m m from rfl]
  rw [vandermonde n m m]

/-- Smoke: `Σ_k C(3,k)·C(4,5−k) = C(7,5) = 21`, `Σ C(4,k)² = C(8,4) = 70`,
    `Σ C(3,k)·C(2,k) = C(5,2) = 10`. -/
theorem vandermonde_smoke : V 3 4 5 = choose 7 5 := by decide
theorem sum_choose_sq_smoke : sumTo 5 (fun k => choose 4 k * choose 4 k) = choose 8 4 := by decide
theorem sum_choose_prod_smoke :
    sumTo 3 (fun k => choose 3 k * choose 2 k) = choose 5 2 := by decide

end E213.Lib.Math.Combinatorics.Vandermonde
