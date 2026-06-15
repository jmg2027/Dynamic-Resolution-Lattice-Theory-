import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.Combinatorics.FibonacciDivisibility

/-!
# Pascal's shallow diagonal sums to Fibonacci: `Σ_k C(n−k, k) = F_{n+1}` (∅-axiom)

The classical bridge between Pascal's triangle and the Fibonacci numbers — the
sum along a *shallow diagonal* `C(n,0)+C(n−1,1)+C(n−2,2)+…` equals `F_{n+1}`
(`diag_eq_fib`).  Genuinely absent (the corpus had no `fib`×`choose` connection).

The diagonal sums satisfy Fibonacci's own recurrence (`diag_rec`:
`diag(n+2)=diag n + diag(n+1)`) via Pascal `C(n+2−k,k)=C(n+1−k,k)+C(n+1−k,k−1)`
reindexing the two pieces into the previous diagonals (with boundary terms
vanishing by `choose 0 (n+2)=0`); the identity then follows by two-step paired
induction matching `fib`.  All ∅-axiom (reuses the `sumTo` reindex toolkit and the
cluster `fib`).
-/

namespace E213.Lib.Math.Combinatorics.PascalDiagonalFib

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
  (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr)
open E213.Lib.Math.Combinatorics.FibonacciDivisibility (fib fib_rec)

/-- Shallow diagonal sum `C(n,0) + C(n−1,1) + C(n−2,2) + …`. -/
def diag (n : Nat) : Nat := sumTo (n + 1) (fun k => choose (n - k) k)

/-- `m ≤ n → (n+1) − m = (n − m) + 1`. -/
theorem succ_sub_of_le : ∀ {n m : Nat}, m ≤ n → (n + 1) - m = (n - m) + 1
  | _, 0, _ => by rw [Nat.sub_zero, Nat.sub_zero]
  | n + 1, m + 1, h => by
    rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
    exact succ_sub_of_le (Nat.le_of_succ_le_succ h)

theorem succ_sub_succ' (n k : Nat) : (n + 1) - (k + 1) = n - k :=
  Nat.succ_sub_succ_eq_sub n k

theorem diag0 : diag 0 = fib 1 := by decide
theorem diag1 : diag 1 = fib 2 := by decide

/-- `diag (n+1) = 1 + Σ_k C(n−k, k+1)` (peel the `k=0` head `C(n+1,0)=1`, reindex). -/
theorem diag_succ_split (n : Nat) :
    diag (n + 1) = 1 + sumTo (n + 1) (fun k => choose (n - k) (k + 1)) := by
  show sumTo (n + 2) (fun k => choose (n + 1 - k) k)
     = 1 + sumTo (n + 1) (fun k => choose (n - k) (k + 1))
  rw [sumTo_split_first (n + 1) (fun k => choose (n + 1 - k) k)]
  show choose (n + 1 - 0) 0 + sumTo (n + 1) (fun k => choose (n + 1 - (k + 1)) (k + 1))
     = 1 + sumTo (n + 1) (fun k => choose (n - k) (k + 1))
  rw [Nat.sub_zero, choose_zero_right]
  rw [sumTo_congr (n + 1)
        (fun k => choose (n + 1 - (k + 1)) (k + 1))
        (fun k => choose (n - k) (k + 1))
        (fun k _ => by
          show choose (n + 1 - (k + 1)) (k + 1) = choose (n - k) (k + 1)
          rw [succ_sub_succ'])]

/-- ★ **Diagonal recurrence**: `diag (n+2) = diag n + diag (n+1)` — the shallow
    diagonals satisfy Fibonacci's recurrence (Pascal split + `sumTo` reindex). -/
theorem diag_rec (n : Nat) : diag (n + 2) = diag n + diag (n + 1) := by
  show sumTo (n + 3) (fun k => choose (n + 2 - k) k) = diag n + diag (n + 1)
  rw [sumTo_split_first (n + 2) (fun k => choose (n + 2 - k) k)]
  show choose (n + 2 - 0) 0 + sumTo (n + 2) (fun k => choose (n + 2 - (k + 1)) (k + 1))
     = diag n + diag (n + 1)
  rw [Nat.sub_zero, choose_zero_right]
  rw [sumTo_congr (n + 2)
        (fun k => choose (n + 2 - (k + 1)) (k + 1))
        (fun k => choose (n + 1 - k) (k + 1))
        (fun k _ => by
          show choose (n + 2 - (k + 1)) (k + 1) = choose (n + 1 - k) (k + 1)
          rw [succ_sub_succ'])]
  rw [sumTo_succ (n + 1) (fun k => choose (n + 1 - k) (k + 1))]
  show 1 + (sumTo (n + 1) (fun k => choose (n + 1 - k) (k + 1))
            + choose (n + 1 - (n + 1)) (n + 1 + 1))
     = diag n + diag (n + 1)
  rw [Nat.sub_self, show choose 0 (n + 1 + 1) = 0 from rfl, Nat.add_zero]
  rw [sumTo_congr (n + 1)
        (fun k => choose (n + 1 - k) (k + 1))
        (fun k => choose (n - k) k + choose (n - k) (k + 1))
        (fun k hk => by
          show choose (n + 1 - k) (k + 1) = choose (n - k) k + choose (n - k) (k + 1)
          rw [succ_sub_of_le (Nat.le_of_lt_succ hk), choose_succ_succ])]
  rw [← sumTo_add_func (n + 1)
        (fun k => choose (n - k) k) (fun k => choose (n - k) (k + 1))]
  show 1 + (sumTo (n + 1) (fun k => choose (n - k) k)
            + sumTo (n + 1) (fun k => choose (n - k) (k + 1)))
     = diag n + diag (n + 1)
  rw [show sumTo (n + 1) (fun k => choose (n - k) k) = diag n from rfl]
  rw [Nat.add_comm 1 (diag n + sumTo (n + 1) (fun k => choose (n - k) (k + 1)))]
  rw [Nat.add_assoc (diag n) (sumTo (n + 1) (fun k => choose (n - k) (k + 1))) 1]
  rw [Nat.add_comm (sumTo (n + 1) (fun k => choose (n - k) (k + 1))) 1]
  rw [← diag_succ_split n]

/-- Pair form for two-step induction. -/
theorem diag_eq_fib_pair : ∀ n : Nat,
    (diag n = fib (n + 1)) ∧ (diag (n + 1) = fib (n + 2)) := by
  intro n
  induction n with
  | zero => exact ⟨diag0, diag1⟩
  | succ k ih =>
    obtain ⟨ihk, ihk1⟩ := ih
    refine ⟨ihk1, ?_⟩
    rw [diag_rec k, ihk, ihk1, fib_rec (k + 1)]

/-- ★★ **Pascal shallow-diagonal = Fibonacci**: `Σ_k C(n−k, k) = F_{n+1}`. -/
theorem diag_eq_fib (n : Nat) : diag n = fib (n + 1) :=
  (diag_eq_fib_pair n).1

end E213.Lib.Math.Combinatorics.PascalDiagonalFib
