import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem

/-!
# The binomial-mean identity `Σ_{k} k·C(m,k) = m·2^{m-1}` (∅-axiom)

The weighted row sum of Pascal's triangle: `Σ_{k=0}^{m} k·C(m,k) = m·2^{m-1}` — equivalently the
mean of a `Binomial(m, ½)` variable is `m/2`.  Written for `m = n+1` to keep `2^{m-1} = 2^n`
literal, in the cleared form `Σ_{k=0}^{n} (k+1)·C(n+1, k+1) = (n+1)·2^n`.

Clean composition of three existing bricks: the absorption identity
`(k+1)·C(n+1,k+1) = (n+1)·C(n,k)` (`choose_succ_mul`), the constant-pull `sumTo_mul_left`, and the
row sum `Σ_k C(n,k) = 2^n` (`pascal_row_sum`).  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.BinomialMean

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_succ_mul)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_mul_left sumTo_congr pascal_row_sum)

/-- ★★★ **Binomial-mean identity** (cleared, `m = n+1`):
    `Σ_{k=0}^{n} (k+1)·C(n+1, k+1) = (n+1)·2^n`.

    The left sum ranges over the nonzero-weight terms `j = k+1 ∈ {1,…,n+1}` of
    `Σ_{j} j·C(n+1, j)`; the `j = 0` term contributes `0`, so this is the full weighted row sum
    `Σ_j j·C(m,j) = m·2^{m-1}` with `m = n+1`. -/
theorem binomial_weighted_row_sum (n : Nat) :
    sumTo (n + 1) (fun k => (k + 1) * choose (n + 1) (k + 1)) = (n + 1) * 2 ^ n := by
  -- absorb each term: `(k+1)·C(n+1,k+1) = (n+1)·C(n,k)`
  rw [sumTo_congr (n + 1)
        (fun k => (k + 1) * choose (n + 1) (k + 1))
        (fun k => (n + 1) * choose n k)
        (fun k _ => choose_succ_mul n k)]
  -- pull out the constant `(n+1)` and apply the row sum
  rw [← sumTo_mul_left (n + 1) (n + 1) (fun k => choose n k), pascal_row_sum n]

/-- Smoke: `Σ_{j=1}^{4} j·C(4,j) = 1·4 + 2·6 + 3·4 + 4·1 = 32 = 4·2³`. -/
theorem binomial_mean_smoke :
    sumTo 4 (fun k => (k + 1) * choose 4 (k + 1)) = 4 * 2 ^ 3 := by decide

end E213.Lib.Math.Combinatorics.BinomialMean
