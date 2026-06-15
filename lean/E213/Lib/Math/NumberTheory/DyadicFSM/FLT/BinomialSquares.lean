import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Vandermonde
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Tactic.NatHelper

/-!
# Sum of binomial squares: `Σ_{k=0}^{n} C(n,k)² = C(2n,n)` (∅-axiom)

A clean corollary of the corpus's **Vandermonde** identity
(`vand n n n = C(n+n, n)`) + binomial symmetry: the convolution summand
`C(n,j)·C(n,n−j)` collapses to `C(n,j)²` (since `C(n,n−j)=C(n,j)` for `j ≤ n`), so
the central-binomial value `C(2n,n)` equals the sum of squares of the `n`-th
binomial row.  Genuinely absent (the corpus `BinomSymm` is for a *different*
binomial `binom`, not the FLT `choose`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialSquares

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_symm_sum)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
  (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_congr)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Vandermonde
  (vand vandermonde)

/-- Reflection of the summand: for `j ≤ n`, `C(n, n−j) = C(n, j)`. -/
theorem choose_refl {n j : Nat} (hj : j ≤ n) : choose n (n - j) = choose n j :=
  (choose_symm_sum n j (n - j) (E213.Tactic.NatHelper.add_sub_of_le hj)).symm

/-- ★ **Sum of binomial squares** — `Σ_{k=0}^{n} C(n,k)² = C(2n, n)`.
    A clean corollary: Vandermonde `vand n n n = C(n+n, n)` with the convolution
    summand `C(n,j)·C(n,n−j)` collapsed to `C(n,j)²` by binomial symmetry. -/
theorem sum_binom_sq (n : Nat) :
    sumTo (n + 1) (fun k => choose n k * choose n k) = choose (2 * n) n := by
  have hcongr :
      sumTo (n + 1) (fun k => choose n k * choose n k)
        = sumTo (n + 1) (fun j => choose n j * choose n (n - j)) := by
    apply sumTo_congr
    intro j hj
    have hjle : j ≤ n := Nat.le_of_lt_succ hj
    show choose n j * choose n j = choose n j * choose n (n - j)
    rw [choose_refl hjle]
  rw [hcongr]
  -- `sumTo (n+1) (fun j => C(n,j)·C(n,n−j)) = vand n n n` by definition.
  show vand n n n = choose (2 * n) n
  rw [vandermonde n n n]
  rw [E213.Tactic.NatHelper.two_mul n]

/-- Smoke checks: `Σ C(3,k)² = C(6,3) = 20`, `Σ C(4,k)² = C(8,4) = 70`. -/
theorem sum_binom_sq_smoke :
    sumTo 4 (fun k => choose 3 k * choose 3 k) = choose 6 3
    ∧ sumTo 5 (fun k => choose 4 k * choose 4 k) = choose 8 4 := by
  decide

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialSquares
