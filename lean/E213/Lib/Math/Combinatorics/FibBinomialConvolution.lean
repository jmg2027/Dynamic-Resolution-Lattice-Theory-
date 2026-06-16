import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.Combinatorics.FibonacciDivisibility

/-!
# Fibonacci–binomial convolution `Σ C(n,k)·Fₖ = F₂ₙ` (∅-axiom)

A genuinely deep cross-cluster identity connecting the binomial coefficients and
the Fibonacci numbers:

  ★ `fib_binom_sum` : `Σ_{k=0}^{n} C(n,k)·Fₖ = F_{2n}`.
  ★ `fib_binom_sum_shift` : `Σ_{k=0}^{n} C(n,k)·F_{k+1} = F_{2n+1}` (the paired
    companion — needed because the Pascal-split step mixes the two).

Proof: generalize to `U n s = Σ_{k=0}^{n} C(n,k)·F_{k+s}`, establish the shift
recurrences `U(n+1) s = U n s + U n (s+1)` (Pascal split + `sumTo` reindex, last
term vanishing by `choose_eq_zero_of_lt`) and `U n (s+2) = U n s + U n (s+1)`
(Fibonacci recurrence inside the sum), then a paired induction on the invariant
`(U n 0 = F_{2n}, U n 1 = F_{2n+1})`.

Genuinely absent.  NOTE (propext landmine): `Nat.add_mul` leaks `propext` (while
`Nat.mul_add` is clean!) — the Pascal-split `add_mul` step uses the PURE
`E213.Tactic.NatHelper.add_mul` twin.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.FibBinomialConvolution

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
  (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr)
open E213.Lib.Math.Combinatorics.FibonacciDivisibility (fib fib_rec)
open E213.Tactic.NatHelper (add_mul)

/-- Shifted binomial-Fibonacci convolution `U n s = Σ_{k=0}^{n} C(n,k)·fib(k+s)`. -/
def U (n s : Nat) : Nat := sumTo (n + 1) (fun k => choose n k * fib (k + s))

/-- Peel the `k=0` head: `U n s = fib s + Σ_{k<n} C(n,k+1)·fib(k+1+s)`. -/
theorem U_split_head (n s : Nat) :
    U n s = fib s + sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s)) := by
  show sumTo (n + 1) (fun k => choose n k * fib (k + s))
     = fib s + sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s))
  rw [sumTo_split_first n (fun k => choose n k * fib (k + s))]
  show choose n 0 * fib (0 + s) + sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s))
     = fib s + sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s))
  rw [choose_zero_right, Nat.one_mul, Nat.zero_add]

/-- Shift recurrence: `U (n+1) s = U n s + U n (s+1)` (Pascal split + reindex). -/
theorem U_rec (n s : Nat) : U (n + 1) s = U n s + U n (s + 1) := by
  show sumTo (n + 2) (fun k => choose (n + 1) k * fib (k + s))
     = U n s + U n (s + 1)
  rw [sumTo_split_first (n + 1) (fun k => choose (n + 1) k * fib (k + s))]
  show choose (n + 1) 0 * fib (0 + s)
       + sumTo (n + 1) (fun k => choose (n + 1) (k + 1) * fib (k + 1 + s))
     = U n s + U n (s + 1)
  rw [choose_zero_right, Nat.one_mul, Nat.zero_add]
  rw [sumTo_congr (n + 1)
        (fun k => choose (n + 1) (k + 1) * fib (k + 1 + s))
        (fun k => choose n k * fib (k + 1 + s) + choose n (k + 1) * fib (k + 1 + s))
        (fun k _ => by
          show choose (n + 1) (k + 1) * fib (k + 1 + s)
             = choose n k * fib (k + 1 + s) + choose n (k + 1) * fib (k + 1 + s)
          rw [choose_succ_succ n k, add_mul])]
  rw [← sumTo_add_func (n + 1)
        (fun k => choose n k * fib (k + 1 + s))
        (fun k => choose n (k + 1) * fib (k + 1 + s))]
  have hA : sumTo (n + 1) (fun k => choose n k * fib (k + 1 + s))
          = U n (s + 1) := by
    show sumTo (n + 1) (fun k => choose n k * fib (k + 1 + s))
       = sumTo (n + 1) (fun k => choose n k * fib (k + (s + 1)))
    exact sumTo_congr (n + 1)
      (fun k => choose n k * fib (k + 1 + s))
      (fun k => choose n k * fib (k + (s + 1)))
      (fun k _ => by
        show choose n k * fib (k + 1 + s) = choose n k * fib (k + (s + 1))
        rw [show k + 1 + s = k + (s + 1) from by ring_nat])
  have hB : sumTo (n + 1) (fun k => choose n (k + 1) * fib (k + 1 + s))
          = sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s)) := by
    rw [sumTo_succ n (fun k => choose n (k + 1) * fib (k + 1 + s))]
    show sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s))
         + choose n (n + 1) * fib (n + 1 + s)
       = sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s))
    rw [choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n), Nat.zero_mul, Nat.add_zero]
  rw [hA, hB]
  rw [U_split_head n s]
  rw [Nat.add_comm (U n (s + 1)) (sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s)))]
  rw [← Nat.add_assoc (fib s)
        (sumTo n (fun k => choose n (k + 1) * fib (k + 1 + s))) (U n (s + 1))]

/-- `U n (s+2) = U n s + U n (s+1)` (Fibonacci recurrence inside the sum). -/
theorem U_shift2 (n s : Nat) : U n (s + 2) = U n s + U n (s + 1) := by
  show sumTo (n + 1) (fun k => choose n k * fib (k + (s + 2)))
     = U n s + U n (s + 1)
  rw [sumTo_congr (n + 1)
        (fun k => choose n k * fib (k + (s + 2)))
        (fun k => choose n k * fib (k + s) + choose n k * fib (k + (s + 1)))
        (fun k _ => by
          show choose n k * fib (k + (s + 2))
             = choose n k * fib (k + s) + choose n k * fib (k + (s + 1))
          rw [show k + (s + 2) = (k + s) + 2 from by ring_nat, fib_rec (k + s)]
          rw [Nat.mul_add]
          rw [show (k + s) + 1 = k + (s + 1) from by ring_nat])]
  rw [← sumTo_add_func (n + 1)
        (fun k => choose n k * fib (k + s))
        (fun k => choose n k * fib (k + (s + 1)))]
  show (sumTo (n + 1) (fun k => choose n k * fib (k + s)))
       + (sumTo (n + 1) (fun k => choose n k * fib (k + (s + 1))))
     = U n s + U n (s + 1)
  rfl

/-- Paired invariant: `U n 0 = F_{2n}` AND `U n 1 = F_{2n+1}`, by induction on `n`. -/
theorem U_eq_fib_pair : ∀ n : Nat,
    (U n 0 = fib (2 * n)) ∧ (U n 1 = fib (2 * n + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show U 0 0 = fib (2 * 0); decide
    · show U 0 1 = fib (2 * 0 + 1); decide
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [U_rec k 0, ih0, ih1]
      show fib (2 * k) + fib (2 * k + 1) = fib (2 * (k + 1))
      rw [show 2 * (k + 1) = (2 * k) + 2 from by ring_nat, fib_rec (2 * k)]
    · rw [U_rec k 1, U_shift2 k 0]
      rw [ih0, ih1]
      show fib (2 * k + 1) + (fib (2 * k) + fib (2 * k + 1)) = fib (2 * (k + 1) + 1)
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring_nat, fib_rec (2 * k + 1)]
      rw [show (2 * k + 1) + 1 = (2 * k) + 2 from by ring_nat, fib_rec (2 * k)]

/-- ★ **Fibonacci–binomial convolution**: `Σ_{k=0}^{n} C(n,k)·F_k = F_{2n}`. -/
theorem fib_binom_sum (n : Nat) :
    sumTo (n + 1) (fun k => choose n k * fib k) = fib (2 * n) :=
  (U_eq_fib_pair n).1

/-- ★ **Companion**: `Σ_{k=0}^{n} C(n,k)·F_{k+1} = F_{2n+1}`. -/
theorem fib_binom_sum_shift (n : Nat) :
    sumTo (n + 1) (fun k => choose n k * fib (k + 1)) = fib (2 * n + 1) :=
  (U_eq_fib_pair n).2

/-- Smoke: `Σ C(3,k)·F_k = F_6 = 8`. -/
theorem fib_binom_smoke : sumTo 4 (fun k => choose 3 k * fib k) = fib 6 := by decide

end E213.Lib.Math.Combinatorics.FibBinomialConvolution
