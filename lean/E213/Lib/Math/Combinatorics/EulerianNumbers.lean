import E213.Lib.Math.Combinatorics.Permutations
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# Eulerian numbers `A(n,k)` — row sum + Worpitzky's identity (∅-axiom)

The Eulerian numbers count permutations of `n` by number of ascents.  Recurrence
`A(0,0)=1`, `A(0,k+1)=0`, `A(n+1,0)=1`, `A(n+1,k+1) = (k+2)·A(n,k+1) + (n−k)·A(n,k)`.

  ★ `eulerian_row_sum` : `Σ_{k=0}^{n} A(n,k) = n!` (general — every permutation has
    some ascent count).  Key fact: the coefficient of each `A(n,j)` across row `n+1`
    telescopes, `(j+1) + (n−j) = n+1` (`coeff_collapse`), so the row sum scales by
    `(n+1)`.  Same head-peel/reindex template as `StirlingFirstKind.lean`.
  ★★ `worpitzky_one/two/three` : Worpitzky's identity `xⁿ = Σ_{k} A(n,k)·C(x+k, n)`
    as genuine polynomial identities in `x` for n = 1, 2, 3 (the n=2,3 cases by a
    pure-Pascal basis change `expand3` + a closed-form anchor `closed3` proven by
    induction on `x`).

The fully-general `∀ n, ∀ x` Worpitzky (needing the Eulerian/binomial convolution)
is an open frontier; the general row sum and the general-`x` per-`n` Worpitzky are
the closed results here.  All ∅-axiom.  Genuinely absent.
-/

namespace E213.Lib.Math.Combinatorics.EulerianNumbers

open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr sumTo_mul_left)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_one_right choose_succ_succ choose_zero_right)
open E213.Tactic.NatHelper (add_sub_of_le sub_add_cancel)

/-- Eulerian numbers `A(n,k)`: permutations of `n` by number of ascents. -/
def eulerian : Nat → Nat → Nat
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | _ + 1, 0     => 1
  | n + 1, k + 1 => (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k

/-! ## Table smoke checks (the recurrence reproduces the standard table) -/

theorem tbl_col0 : eulerian 3 0 = 1 ∧ eulerian 4 0 = 1 ∧ eulerian 5 0 = 1 := by decide
theorem tbl_row3 :
    eulerian 3 0 = 1 ∧ eulerian 3 1 = 4 ∧ eulerian 3 2 = 1 ∧ eulerian 3 3 = 0 := by decide
theorem tbl_row4 :
    eulerian 4 0 = 1 ∧ eulerian 4 1 = 11 ∧ eulerian 4 2 = 11 ∧ eulerian 4 3 = 1
      ∧ eulerian 4 4 = 0 := by decide
theorem tbl_row5 :
    eulerian 5 0 = 1 ∧ eulerian 5 1 = 26 ∧ eulerian 5 2 = 66 ∧ eulerian 5 3 = 26
      ∧ eulerian 5 4 = 1 := by decide

/-- `A(m, k) = 0` when `m < k` (a permutation of `m` has at most `m−1` ascents). -/
theorem eulerian_zero_above : ∀ {m k : Nat}, m < k → eulerian m k = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | m + 1, k + 1, h => by
      have hmk : m < k := Nat.lt_of_succ_lt_succ h
      show (k + 2) * eulerian m (k + 1) + (m - k) * eulerian m k = 0
      rw [eulerian_zero_above (Nat.lt_succ_of_lt hmk), eulerian_zero_above hmk,
          Nat.mul_zero, Nat.mul_zero, Nat.add_zero]

/-- `1 + Σ_{k=0}^{n} (k+2)·A(n,k+1) = Σ_{j=0}^{n} (j+1)·A(n,j)` (reindex of the
    `(k+2)·A(n,k+1)` part of the tail; top term `(n+2)·A(n,n+1) = 0`). -/
theorem head_reindex (n : Nat) :
    1 + sumTo (n + 1) (fun k => (k + 2) * eulerian n (k + 1))
      = sumTo (n + 1) (fun j => (j + 1) * eulerian n j) := by
  have htop : sumTo (n + 1) (fun k => (k + 2) * eulerian n (k + 1))
                = sumTo n (fun k => (k + 2) * eulerian n (k + 1)) := by
    show sumTo n (fun k => (k + 2) * eulerian n (k + 1)) + (n + 2) * eulerian n (n + 1)
       = sumTo n (fun k => (k + 2) * eulerian n (k + 1))
    rw [eulerian_zero_above (Nat.lt_succ_self n), Nat.mul_zero, Nat.add_zero]
  rw [htop]
  rw [sumTo_split_first n (fun j => (j + 1) * eulerian n j)]
  show 1 + sumTo n (fun k => (k + 2) * eulerian n (k + 1))
     = (0 + 1) * eulerian n 0 + sumTo n (fun k => (k + 1 + 1) * eulerian n (k + 1))
  rw [show eulerian n 0 = 1 by cases n <;> rfl, Nat.zero_add, Nat.one_mul]

/-- Pointwise coefficient collapse: for `j ≤ n`, `(j+1)·A + (n−j)·A = (n+1)·A`. -/
theorem coeff_collapse {n j : Nat} (h : j ≤ n) :
    (j + 1) * eulerian n j + (n - j) * eulerian n j = (n + 1) * eulerian n j := by
  rw [← E213.Tactic.NatHelper.add_mul (j + 1) (n - j) (eulerian n j)]
  have hc : (j + 1) + (n - j) = n + 1 := by
    rw [Nat.add_comm j 1, Nat.add_assoc 1 j (n - j), add_sub_of_le h, Nat.add_comm 1 n]
  rw [hc]

/-- ★ **Eulerian row sum**: `Σ_{k=0}^{n} A(n,k) = n!`. -/
theorem eulerian_row_sum : ∀ n, sumTo (n + 1) (fun k => eulerian n k) = fact n
  | 0 => by
      show (0 : Nat) + eulerian 0 0 = fact 0
      show (0 : Nat) + 1 = 1
      rfl
  | n + 1 => by
      rw [sumTo_split_first (n + 1) (fun k => eulerian (n + 1) k)]
      show eulerian (n + 1) 0
             + sumTo (n + 1) (fun k => eulerian (n + 1) (k + 1))
           = fact (n + 1)
      show (1 : Nat)
             + sumTo (n + 1) (fun k => eulerian (n + 1) (k + 1))
           = fact (n + 1)
      rw [sumTo_congr (n + 1)
            (fun k => eulerian (n + 1) (k + 1))
            (fun k => (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k)
            (fun k _ => rfl)]
      rw [← sumTo_add_func (n + 1)
            (fun k => (k + 2) * eulerian n (k + 1))
            (fun k => (n - k) * eulerian n k)]
      rw [← Nat.add_assoc (1 : Nat)
            (sumTo (n + 1) (fun k => (k + 2) * eulerian n (k + 1)))
            (sumTo (n + 1) (fun k => (n - k) * eulerian n k))]
      rw [head_reindex n]
      rw [sumTo_add_func (n + 1)
            (fun j => (j + 1) * eulerian n j)
            (fun k => (n - k) * eulerian n k)]
      rw [sumTo_congr (n + 1)
            (fun j => (j + 1) * eulerian n j + (n - j) * eulerian n j)
            (fun j => (n + 1) * eulerian n j)
            (fun j hj => coeff_collapse (Nat.le_of_lt_succ hj))]
      rw [← sumTo_mul_left (n + 1) (n + 1) (fun j => eulerian n j)]
      rw [eulerian_row_sum n]
      show (n + 1) * fact n = fact (n + 1)
      rfl

theorem rowsum_smoke3 : sumTo 4 (fun k => eulerian 3 k) = fact 3 := by decide
theorem rowsum_smoke4 : sumTo 5 (fun k => eulerian 4 k) = fact 4 := by decide

/-! ## Worpitzky's identity `xⁿ = Σ_{k=0}^{n−1} A(n,k)·C(x+k, n)` -/

theorem worp_n1 : (5:Nat) ^ 1 = sumTo 1 (fun k => eulerian 1 k * choose (5 + k) 1) := by decide
theorem worp_n2 : (3:Nat) ^ 2 = sumTo 2 (fun k => eulerian 2 k * choose (3 + k) 2) := by decide
theorem worp_n3 : (2:Nat) ^ 3 = sumTo 3 (fun k => eulerian 3 k * choose (2 + k) 3) := by decide
theorem worp_n4 : (3:Nat) ^ 4 = sumTo 4 (fun k => eulerian 4 k * choose (3 + k) 4) := by decide

/-- ★ **Worpitzky at n = 1** (general `x`): `x¹ = C(x, 1) = x`. -/
theorem worpitzky_one (x : Nat) :
    x ^ 1 = sumTo 1 (fun k => eulerian 1 k * choose (x + k) 1) := by
  show x ^ 1 = (0 : Nat) + eulerian 1 0 * choose (x + 0) 1
  show x ^ 1 = (0 : Nat) + 1 * choose (x + 0) 1
  rw [Nat.zero_add, Nat.one_mul, Nat.add_zero, choose_one_right, Nat.pow_one]

/-- Helper: `C(x,2) + C(x+1,2) = x·x`.  Induction on `x` via Pascal. -/
theorem choose2_add (x : Nat) : choose x 2 + choose (x + 1) 2 = x * x := by
  induction x with
  | zero => rfl
  | succ m ih =>
      rw [show choose (m + 1 + 1) 2 = choose (m + 1) 1 + choose (m + 1) 2
            from choose_succ_succ (m + 1) 1]
      rw [show choose (m + 1) 2 = choose m 1 + choose m 2
            from choose_succ_succ m 1]
      rw [choose_one_right (m + 1), choose_one_right m]
      have ih' : choose m 2 + (m + choose m 2) = m * m := by
        rw [show choose (m + 1) 2 = choose m 1 + choose m 2
              from choose_succ_succ m 1, choose_one_right m] at ih
        exact ih
      have key : (m + choose m 2) + ((m + 1) + (m + choose m 2))
                   = (choose m 2 + (m + choose m 2)) + (m + m + 1) := by ring_nat
      rw [key, ih']
      show m * m + (m + m + 1) = (m + 1) * (m + 1)
      ring_nat

/-- ★ **Worpitzky at n = 2** (general `x`): `x² = C(x,2) + C(x+1,2)`. -/
theorem worpitzky_two (x : Nat) :
    x ^ 2 = sumTo 2 (fun k => eulerian 2 k * choose (x + k) 2) := by
  show x ^ 2 = ((0 : Nat) + eulerian 2 0 * choose (x + 0) 2)
                 + eulerian 2 1 * choose (x + 1) 2
  show x ^ 2 = ((0 : Nat) + 1 * choose (x + 0) 2) + 1 * choose (x + 1) 2
  rw [Nat.zero_add, Nat.one_mul, Nat.one_mul, Nat.add_zero]
  rw [show x ^ 2 = x * x from by rw [Nat.pow_two]]
  exact (choose2_add x).symm

/-- Pure-Pascal expansion of the Worpitzky-3 sum into a `C(x,3)/C(x,2)` basis:
    `C(x,3) + 4·C(x+1,3) + C(x+2,3) = 6·C(x,3) + 6·C(x,2) + x`. -/
theorem expand3 (x : Nat) :
    choose x 3 + 4 * choose (x + 1) 3 + choose (x + 2) 3
      = 6 * choose x 3 + 6 * choose x 2 + x := by
  rw [show choose (x + 1) 3 = choose x 2 + choose x 3 from choose_succ_succ x 2]
  rw [show choose (x + 2) 3 = choose (x + 1) 2 + choose (x + 1) 3
        from choose_succ_succ (x + 1) 2]
  rw [show choose (x + 1) 2 = choose x 1 + choose x 2 from choose_succ_succ x 1]
  rw [show choose (x + 1) 3 = choose x 2 + choose x 3 from choose_succ_succ x 2]
  rw [choose_one_right x]
  ring_nat

/-- Closed-form anchor: `6·C(x,3) + 6·C(x,2) + x = x³`.  Induction on `x`. -/
theorem closed3 (x : Nat) : 6 * choose x 3 + 6 * choose x 2 + x = x * x * x := by
  induction x with
  | zero => rfl
  | succ m ih =>
      rw [show choose (m + 1) 3 = choose m 2 + choose m 3 from choose_succ_succ m 2]
      rw [show choose (m + 1) 2 = choose m 1 + choose m 2 from choose_succ_succ m 1]
      rw [choose_one_right m]
      have hq6 : 6 * choose m 2 + 3 * m = 3 * (m * m) := by
        have h2 : choose m 2 + (m + choose m 2) = m * m := by
          have e : choose (m + 1) 2 = m + choose m 2 := by
            rw [choose_succ_succ m 1, choose_one_right m]
          rw [← e]; exact choose2_add m
        calc 6 * choose m 2 + 3 * m
            = 3 * (choose m 2 + (m + choose m 2)) := by ring_nat
          _ = 3 * (m * m) := by rw [h2]
      calc 6 * (choose m 2 + choose m 3) + 6 * (m + choose m 2) + (m + 1)
          = (6 * choose m 3 + 6 * choose m 2 + m)
              + (6 * choose m 2 + 3 * m) + (3 * m + 1) := by ring_nat
        _ = (m * m * m) + (3 * (m * m)) + (3 * m + 1) := by rw [ih, hq6]
        _ = (m + 1) * (m + 1) * (m + 1) := by ring_nat

/-- ★★ **Worpitzky at n = 3** (general `x`): `x³ = C(x,3) + 4·C(x+1,3) + C(x+2,3)`. -/
theorem worpitzky_three (x : Nat) :
    x ^ 3 = sumTo 3 (fun k => eulerian 3 k * choose (x + k) 3) := by
  show x ^ 3 = (((0 : Nat) + eulerian 3 0 * choose (x + 0) 3)
                 + eulerian 3 1 * choose (x + 1) 3)
                 + eulerian 3 2 * choose (x + 2) 3
  show x ^ 3 = (((0 : Nat) + 1 * choose (x + 0) 3)
                 + 4 * choose (x + 1) 3)
                 + 1 * choose (x + 2) 3
  rw [Nat.zero_add, Nat.one_mul, Nat.one_mul, Nat.add_zero]
  rw [show x ^ 3 = x * x * x from by rw [Nat.pow_succ, Nat.pow_two]]
  rw [expand3 x]
  exact (closed3 x).symm

end E213.Lib.Math.Combinatorics.EulerianNumbers
