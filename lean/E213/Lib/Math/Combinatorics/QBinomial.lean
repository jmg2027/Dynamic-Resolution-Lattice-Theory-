import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial

/-!
# q-binomial (Gaussian binomial) coefficients `[n choose k]_q` (∅-axiom)

The Gaussian binomial `[n choose k]_q` evaluated at an integer `q : Int`, via the
q-Pascal recurrence
  `[n, 0]_q = 1`,  `[0, k+1]_q = 0`,  `[n+1, k+1]_q = q^(k+1)·[n, k+1]_q + [n, k]_q`.

  * ★ `qbinom_pascal` — the q-Pascal recurrence (general).
  * ★ `qbinom_q1` — `qbinom 1 n k = choose n k` (the q→1 limit is the ordinary
    binomial; **general**, by induction matching the Pascal recursion).
  * `qbinom_table_q2` — concrete values at q=2 (e.g. `[4,2]_2 = 35`).
  * `qbinom_symm_table` — symmetry `[n,k]_q = [n,n−k]_q` (table; the general proof
    needs the dual q-Pascal `[n+1,k+1]_q = [n,k]_q + q^(n−k)·[n,k+1]_q`, an open item).

Genuinely absent (the corpus had only ordinary `choose`; no q-analog).  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.QBinomial

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_zero_succ choose_succ_succ)

/-- Integer power helper, structural (controls reduction).  `qpow q k = q^k`. -/
def qpow (q : Int) : Nat → Int
  | 0     => 1
  | k + 1 => qpow q k * q

/-- `qpow q (k+1) = qpow q k * q` — definitional. -/
theorem qpow_succ (q : Int) (k : Nat) : qpow q (k + 1) = qpow q k * q := rfl

/-- Gaussian binomial coefficient at value `q : Int`, via q-Pascal. -/
def qbinom (q : Int) : Nat → Nat → Int
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => qpow q (k + 1) * qbinom q n (k + 1) + qbinom q n k

/-- `[n, 0]_q = 1`. -/
theorem qbinom_zero_right (q : Int) (n : Nat) : qbinom q n 0 = 1 := by
  cases n <;> rfl

/-- `[0, k+1]_q = 0`. -/
theorem qbinom_zero_succ (q : Int) (k : Nat) : qbinom q 0 (k + 1) = 0 := rfl

/-- ★ **q-Pascal**: `[n+1, k+1]_q = q^(k+1)·[n, k+1]_q + [n, k]_q`. -/
theorem qbinom_pascal (q : Int) (n k : Nat) :
    qbinom q (n + 1) (k + 1) = qpow q (k + 1) * qbinom q n (k + 1) + qbinom q n k := rfl

/-- `qpow 1 k = 1`. -/
theorem qpow_one (k : Nat) : qpow (1 : Int) k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [qpow_succ, ih]; rfl

/-- ★ **q→1 limit**: `qbinom 1 n k = choose n k` (general, by induction matching the
    Pascal recursion). -/
theorem qbinom_q1 : ∀ (n k : Nat), qbinom (1 : Int) n k = (choose n k : Int)
  | _,     0     => by rw [qbinom_zero_right, choose_zero_right]; rfl
  | 0,     k + 1 => by rw [qbinom_zero_succ, choose_zero_succ]; rfl
  | n + 1, k + 1 => by
    rw [qbinom_pascal, qpow_one, qbinom_q1 n (k + 1), qbinom_q1 n k,
        choose_succ_succ, Int.ofNat_add]
    generalize (choose n (k + 1) : Int) = a
    generalize (choose n k : Int) = b
    ring_intZ

/-- Concrete q-values at `q = 2`: `[2,1]_2=3, [3,1]_2=7, [3,2]_2=7, [4,2]_2=35, [4,1]_2=15`. -/
theorem qbinom_table_q2 :
    qbinom 2 2 1 = 3 ∧ qbinom 2 3 1 = 7 ∧ qbinom 2 3 2 = 7 ∧
    qbinom 2 4 2 = 35 ∧ qbinom 2 4 1 = 15 := by decide

/-- Symmetry spot-checks `[n,k]_q = [n,n−k]_q` (across q ∈ {2,3,5}). -/
theorem qbinom_symm_table :
    qbinom 2 4 1 = qbinom 2 4 3 ∧ qbinom 2 5 2 = qbinom 2 5 3 ∧
    qbinom 3 4 1 = qbinom 3 4 3 ∧ qbinom 2 6 2 = qbinom 2 6 4 ∧
    qbinom 5 4 1 = qbinom 5 4 3 := by decide

/-- Cross-check vs ordinary binomials at `q = 1`. -/
theorem qbinom_q1_table :
    qbinom 1 4 2 = 6 ∧ qbinom 1 5 2 = 10 ∧ qbinom 1 6 3 = 20 := by decide

end E213.Lib.Math.Combinatorics.QBinomial
