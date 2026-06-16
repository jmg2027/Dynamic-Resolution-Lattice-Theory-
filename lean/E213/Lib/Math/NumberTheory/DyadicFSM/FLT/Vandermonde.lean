import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Tactic.NatHelper

/-!
# Vandermonde's identity (∅-axiom)

`Σ_{j=0}^{k} C(a,j)·C(b,k−j) = C(a+b,k)` — the binomial convolution / addition
formula, a genuine deep combinatorial identity (not a table value).  Proven by
induction on `a` using the `sumTo` reindex toolkit:

  * the **peel-first** primitive `sumTo_split_first` *is* the reindex — run forward
    to extract the `j=0` head, run backward (`head_add_tail2`) to recombine;
  * `sumTo_add_func` splits the Pascal-expanded summand `C(a+1,j+1) = C(a,j)+C(a,j+1)`
    into two convolution tails;
  * the `k−j` Nat-subtraction friction dissolves via `Nat.succ_sub_succ`
    (`(m+1)−(j+1) = m−j`), the PURE route (plain `rfl` fails for variable `m`).

All ∅-axiom (no `propext`/`Classical`; no `omega`/`simp`/`rw…at` — the propext
landmines are avoided throughout).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Vandermonde

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_zero_succ choose_succ_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
  (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_add_func sumTo_split_first sumTo_congr)

/-- Vandermonde convolution sum `Σ_{j=0}^{k} C(a,j)·C(b,k−j)`. -/
def vand (a b k : Nat) : Nat := sumTo (k + 1) (fun j => choose a j * choose b (k - j))

/-- Base case `a = 0`: only the `j = 0` term survives (`C(0, j+1) = 0`). -/
theorem vand_zero (b k : Nat) : vand 0 b k = choose b k := by
  show sumTo (k + 1) (fun j => choose 0 j * choose b (k - j)) = choose b k
  rw [sumTo_split_first k (fun j => choose 0 j * choose b (k - j))]
  show choose 0 0 * choose b (k - 0)
       + sumTo k (fun j => choose 0 (j + 1) * choose b (k - (j + 1))) = choose b k
  rw [choose_zero_right]
  have htail : sumTo k (fun j => choose 0 (j + 1) * choose b (k - (j + 1))) = 0 := by
    have heq : sumTo k (fun j => choose 0 (j + 1) * choose b (k - (j + 1)))
         = sumTo k (fun _ => 0) := by
      apply sumTo_congr
      intro j _
      rw [choose_zero_succ, Nat.zero_mul]
    rw [heq]
    clear heq
    induction k with
    | zero => rfl
    | succ k ih => rw [sumTo_succ]; rw [ih]
  rw [htail, Nat.add_zero, Nat.sub_zero, Nat.one_mul]

/-- Split `vand (a+1) b k` into head `C(b,k)` plus two tail sums over `range k`
    (Pascal under the sum, then additivity). -/
theorem vand_succ_split (a b k : Nat) :
    vand (a + 1) b k
      = choose b k
        + (sumTo k (fun j => choose a j * choose b (k - (j + 1)))
          + sumTo k (fun j => choose a (j + 1) * choose b (k - (j + 1)))) := by
  show sumTo (k + 1) (fun j => choose (a + 1) j * choose b (k - j)) = _
  rw [sumTo_split_first k (fun j => choose (a + 1) j * choose b (k - j))]
  show choose (a + 1) 0 * choose b (k - 0)
       + sumTo k (fun j => choose (a + 1) (j + 1) * choose b (k - (j + 1))) = _
  rw [choose_zero_right, Nat.one_mul, Nat.sub_zero]
  rw [sumTo_congr k
        (fun j => choose (a + 1) (j + 1) * choose b (k - (j + 1)))
        (fun j => choose a j * choose b (k - (j + 1))
                  + choose a (j + 1) * choose b (k - (j + 1)))
        (fun j _ => by
          show choose (a + 1) (j + 1) * choose b (k - (j + 1))
             = choose a j * choose b (k - (j + 1))
               + choose a (j + 1) * choose b (k - (j + 1))
          rw [choose_succ_succ, E213.Tactic.NatHelper.add_mul])]
  rw [← sumTo_add_func k
        (fun j => choose a j * choose b (k - (j + 1)))
        (fun j => choose a (j + 1) * choose b (k - (j + 1)))]

/-- Head + second tail recombine into `vand a b k` (`sumTo_split_first` backwards). -/
theorem head_add_tail2 (a b k : Nat) :
    choose b k + sumTo k (fun j => choose a (j + 1) * choose b (k - (j + 1)))
      = vand a b k := by
  show _ = sumTo (k + 1) (fun j => choose a j * choose b (k - j))
  rw [sumTo_split_first k (fun j => choose a j * choose b (k - j))]
  show choose b k + _ = choose a 0 * choose b (k - 0) + _
  rw [choose_zero_right, Nat.one_mul, Nat.sub_zero]

/-- First tail `= vand a b m` when `k = m+1` (via `Nat.succ_sub_succ`). -/
theorem tail1_eq (a b m : Nat) :
    sumTo (m + 1) (fun j => choose a j * choose b ((m + 1) - (j + 1)))
      = vand a b m := by
  show _ = sumTo (m + 1) (fun j => choose a j * choose b (m - j))
  apply sumTo_congr
  intro j _
  show choose a j * choose b ((m + 1) - (j + 1)) = choose a j * choose b (m - j)
  rw [Nat.succ_sub_succ]

/-- ★★★ **Vandermonde's identity** — `Σ_{j=0}^{k} C(a,j)·C(b,k−j) = C(a+b,k)`.  The
    binomial convolution / addition formula, by induction on `a`. -/
theorem vandermonde : ∀ (a b k : Nat), vand a b k = choose (a + b) k
  | 0,     b, k => by rw [vand_zero, Nat.zero_add]
  | a + 1, b, 0 => by
    show sumTo 1 (fun j => choose (a + 1) j * choose b (0 - j)) = choose (a + 1 + b) 0
    show (0 : Nat) + choose (a + 1) 0 * choose b (0 - 0) = choose (a + 1 + b) 0
    rw [choose_zero_right, choose_zero_right, choose_zero_right]
  | a + 1, b, m + 1 => by
    have ih_m  : vand a b m       = choose (a + b) m       := vandermonde a b m
    have ih_m1 : vand a b (m + 1) = choose (a + b) (m + 1) := vandermonde a b (m + 1)
    rw [vand_succ_split a b (m + 1)]
    rw [show choose b (m + 1)
          + (sumTo (m + 1) (fun j => choose a j * choose b ((m + 1) - (j + 1)))
            + sumTo (m + 1) (fun j => choose a (j + 1) * choose b ((m + 1) - (j + 1))))
        = (choose b (m + 1)
            + sumTo (m + 1) (fun j => choose a (j + 1) * choose b ((m + 1) - (j + 1))))
          + sumTo (m + 1) (fun j => choose a j * choose b ((m + 1) - (j + 1)))
        from by
          rw [Nat.add_comm
                (sumTo (m + 1) (fun j => choose a j * choose b ((m + 1) - (j + 1))))
                (sumTo (m + 1) (fun j => choose a (j + 1) * choose b ((m + 1) - (j + 1)))),
              ← Nat.add_assoc]]
    rw [head_add_tail2 a b (m + 1), tail1_eq a b m, ih_m, ih_m1]
    show choose (a + b) (m + 1) + choose (a + b) m = choose (a + 1 + b) (m + 1)
    rw [show a + 1 + b = (a + b) + 1 from by rw [Nat.add_right_comm a 1 b],
        choose_succ_succ, Nat.add_comm]

/-- Smoke checks: `C(3,·)*C(4,·) ⊛ = C(7,·)`, etc. -/
theorem vand_smoke :
    vand 3 4 2 = choose 7 2 ∧ vand 5 5 5 = choose 10 5 ∧ vand 2 3 3 = choose 5 3 := by
  decide

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Vandermonde
