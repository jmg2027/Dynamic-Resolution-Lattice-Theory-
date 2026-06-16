import E213.Lib.Math.Combinatorics.CatalanBinomial
import E213.Lib.Math.Combinatorics.Catalan
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PolyNatMTactic

/-!
# Narayana numbers `N(n,k)` — triangle, edges, symmetry, row sum (∅-axiom)

The Narayana numbers `N(n,k) = C(n,k)·C(n,k−1)/n` refine the Catalan numbers by
peak count: `Σ_{k=1}^{n} N(n,k) = C_n`.

  * `narayana_table` — the triangle, rows n=1..5: [1],[1,1],[1,3,1],[1,6,6,1],[1,10,20,10,1].
  * ★ `narayana_one` / `narayana_diag` — general edge values `N(n,1) = N(n,n) = 1`.
  * ★ `narayana_symm` — **general row symmetry** `N(n,k) = N(n,n+1−k)` for `1 ≤ k ≤ n`.
  * `narayana_row_sum_table` — `Σ_{k=1}^{n} N(n,k) = catalan n`, verified n=1..7.

The general row sum `Σ_k N(n,k) = catN n` (all n) is open: the `/n` sits inside the
summand, so a general induction must push the division through `sumTo` and relate it
to `catN`'s central-binomial recurrence — left as a frontier.  Genuinely absent
(the `Fractal/Narayana*` modules are an unrelated modular recurrence).

Note (propext): `Nat.sub_sub`/`Nat.add_sub_cancel'` are propext-tainted; the
symmetry proof decomposes `k = 1+j`, `n = (1+j)+m` via `Nat.le.dest` so all index
arithmetic is pure addition (NatHelper twins + `ring_nat`).  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.NarayanaNumbers

open E213.Lib.Math.Combinatorics.Catalan (catalan)
open E213.Lib.Math.Combinatorics.CatalanBinomial (catN)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_succ_succ choose_one_right choose_zero_right choose_self
   choose_eq_zero_of_lt choose_symm_sum)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Tactic.NatHelper (add_sub_cancel_right add_sub_of_le)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)

/-- Narayana number `N(n,k) = C(n,k)·C(n,k−1)/n` (truncating `Nat` division handles
    the `k=0` / `n=0` fractional convention). -/
def narayana (n k : Nat) : Nat := choose n k * choose n (k - 1) / n

/-- The Narayana triangle, rows n = 1..5. -/
theorem narayana_table :
    narayana 1 1 = 1
    ∧ (narayana 2 1 = 1 ∧ narayana 2 2 = 1)
    ∧ (narayana 3 1 = 1 ∧ narayana 3 2 = 3 ∧ narayana 3 3 = 1)
    ∧ (narayana 4 1 = 1 ∧ narayana 4 2 = 6 ∧ narayana 4 3 = 6 ∧ narayana 4 4 = 1)
    ∧ (narayana 5 1 = 1 ∧ narayana 5 2 = 10 ∧ narayana 5 3 = 20
        ∧ narayana 5 4 = 10 ∧ narayana 5 5 = 1) := by decide

/-! ## Row sum `Σ_{k=1}^{n} N(n,k) = catalan n` (verified n = 1..7)

`sumTo n (fun k => narayana n (k+1))` sums the row over `k = 1..n`.  The `k = 0`
slot is excluded — the only one carrying the `1/n`-pollution (`narayana_zero`). -/

theorem narayana_row_sum_table :
    sumTo 1 (fun k => narayana 1 (k + 1)) = catalan 1
    ∧ sumTo 2 (fun k => narayana 2 (k + 1)) = catalan 2
    ∧ sumTo 3 (fun k => narayana 3 (k + 1)) = catalan 3
    ∧ sumTo 4 (fun k => narayana 4 (k + 1)) = catalan 4
    ∧ sumTo 5 (fun k => narayana 5 (k + 1)) = catalan 5
    ∧ sumTo 6 (fun k => narayana 6 (k + 1)) = catalan 6
    ∧ sumTo 7 (fun k => narayana 7 (k + 1)) = catalan 7 := by decide

/-- Same row-sum table against the general central-binomial Catalan `catN`. -/
theorem narayana_row_sum_table_catN :
    sumTo 1 (fun k => narayana 1 (k + 1)) = catN 1
    ∧ sumTo 2 (fun k => narayana 2 (k + 1)) = catN 2
    ∧ sumTo 3 (fun k => narayana 3 (k + 1)) = catN 3
    ∧ sumTo 4 (fun k => narayana 4 (k + 1)) = catN 4
    ∧ sumTo 5 (fun k => narayana 5 (k + 1)) = catN 5
    ∧ sumTo 6 (fun k => narayana 6 (k + 1)) = catN 6
    ∧ sumTo 7 (fun k => narayana 7 (k + 1)) = catN 7 := by decide

/-! ## Boundary + edge values -/

/-- `narayana (n+2) 0 = 0` (the `k=0` slot does not contribute to the row sum). -/
theorem narayana_zero (n : Nat) : narayana (n + 2) 0 = 0 := by
  show choose (n + 2) 0 * choose (n + 2) (0 - 1) / (n + 2) = 0
  rw [choose_zero_right]
  show 1 * choose (n + 2) 0 / (n + 2) = 0
  rw [choose_zero_right, Nat.mul_one]
  exact Nat.div_eq_of_lt (by exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 n))

/-- ★ **Left edge**, general: `narayana (n+1) 1 = 1`. -/
theorem narayana_one (n : Nat) : narayana (n + 1) 1 = 1 := by
  show choose (n + 1) 1 * choose (n + 1) (1 - 1) / (n + 1) = 1
  rw [show (1 : Nat) - 1 = 0 from rfl, choose_zero_right, choose_one_right]
  exact mul_div_cancel_left_pure (n + 1) 1 (Nat.succ_pos n)

/-- ★ **Right edge**, general: `narayana (n+1) (n+1) = 1`. -/
theorem narayana_diag (n : Nat) : narayana (n + 1) (n + 1) = 1 := by
  show choose (n + 1) (n + 1) * choose (n + 1) ((n + 1) - 1) / (n + 1) = 1
  rw [show (n + 1 : Nat) - 1 = n from add_sub_cancel_right n 1, choose_self]
  rw [show choose (n + 1) n = choose (n + 1) 1 from
        (choose_symm_sum (n + 1) n 1 rfl), choose_one_right,
      Nat.mul_comm 1 (n + 1)]
  exact mul_div_cancel_left_pure (n + 1) 1 (Nat.succ_pos n)

/-! ## Symmetry `N(n,k) = N(n, n+1−k)` for `1 ≤ k ≤ n` -/

/-- Numerator symmetry: for `1 ≤ k ≤ n`,
    `C(n,k)·C(n,k−1) = C(n, n+1−k)·C(n, (n+1−k)−1)`. -/
theorem narayana_num_symm (n k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    choose n k * choose n (k - 1) = choose n (n + 1 - k) * choose n ((n + 1 - k) - 1) := by
  obtain ⟨j, hj⟩ := Nat.le.dest h1
  subst hj
  obtain ⟨m, hm⟩ := Nat.le.dest h2
  subst hm
  have hkm1 : 1 + j - 1 = j := by rw [Nat.add_comm 1 j, add_sub_cancel_right]
  have hbig : (1 + j + m) + 1 - (1 + j) = m + 1 := by
    rw [show (1 + j + m) + 1 = (1 + j) + (m + 1) from by ring_nat,
        Nat.add_comm (1 + j) (m + 1), add_sub_cancel_right]
  have hsmall : m + 1 - 1 = m := add_sub_cancel_right m 1
  rw [hkm1, hbig, hsmall]
  have e1 : choose (1 + j + m) (1 + j) = choose (1 + j + m) m :=
    choose_symm_sum (1 + j + m) (1 + j) m rfl
  have e2 : choose (1 + j + m) j = choose (1 + j + m) (m + 1) :=
    choose_symm_sum (1 + j + m) j (m + 1) (by ring_nat)
  rw [e1, e2, Nat.mul_comm]

/-- ★ **Narayana symmetry** `N(n,k) = N(n, n+1−k)` for `1 ≤ k ≤ n`. -/
theorem narayana_symm (n k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    narayana n k = narayana n (n + 1 - k) := by
  show choose n k * choose n (k - 1) / n
     = choose n (n + 1 - k) * choose n ((n + 1 - k) - 1) / n
  rw [narayana_num_symm n k h1 h2]

/-- Smoke for symmetry: `N(5,2) = N(5,4) = 10`. -/
theorem narayana_symm_smoke : narayana 5 2 = narayana 5 4 :=
  narayana_symm 5 2 (by decide) (by decide)

end E213.Lib.Math.Combinatorics.NarayanaNumbers
