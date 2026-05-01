import E213.Math.Cohomology.Dyadic.Legendre213
import E213.Math.Cohomology.Dyadic.FibFSMmod3
import E213.Math.Cohomology.Dyadic.FibFSMmod5
import E213.Math.Cohomology.Dyadic.FibFSMmod7
import E213.Math.Cohomology.Dyadic.FibFSMmod11

/-!
# Fibonacci-Pisano predictor — 4-prime base evidence

  | p  | Legendre | Branch    | π(p) | predict | match |
  |  3 |     2    | inert     |   8  |    8    | TIGHT |
  |  5 |     0    | ramified  |  20  |   20    | TIGHT |
  |  7 |     2    | inert     |  16  |   16    | TIGHT |
  | 11 |     1    | split     |  10  |   10    | TIGHT |

Fibonacci-Pisano formula:
  legendre(5, p) = 0 (ramified)  ⇒  π(p) = 4p
  legendre(5, p) = 1 (split, QR) ⇒  π(p) = p - 1
  legendre(5, p) = 2 (inert, NQR) ⇒  π(p) = 2(p + 1)

Compare to Pell-Pisano (same lens, different formula):
  ramified  ⇒  2p          (Pell)  vs.  4p         (Fibonacci)
  split     ⇒  (p-1)/2     (Pell)  vs.  p-1        (Fibonacci)
  inert     ⇒  p+1         (Pell)  vs.  2(p+1)     (Fibonacci)

Fibonacci formulas are exactly **2×** the Pell formulas in each
branch — reflecting the different normalisation of the Fibonacci
recurrence (no `2a` term) versus Pell.  The Legendre lens fires
identically, but the period scaling differs.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- 213-native Fibonacci-Pisano period predictor for Δ = 5. -/
def fib_pisano_predict (p : Nat) (hp : 1 < p) : Nat :=
  let leg := (legendre213 5 p hp).val
  if leg = 0 then 4 * p              -- ramified
  else if leg = 1 then p - 1         -- split (QR)
  else 2 * (p + 1)                   -- inert (NQR)

/-- ★★★★★★ Predictor matches TIGHT Fibonacci period at all 4 cases. -/
theorem fib_pisano_predict_correct :
    fib_pisano_predict 3 (by decide) = 8
    ∧ fib_pisano_predict 5 (by decide) = 20
    ∧ fib_pisano_predict 7 (by decide) = 16
    ∧ fib_pisano_predict 11 (by decide) = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ The Legendre lens-driven Fibonacci predictor REALISES
    the actual Fibonacci bit periods at all 4 primes. -/
theorem fib_pisano_predict_realises :
    (∀ k, fibFSMmod3.bits (k + fib_pisano_predict 3 (by decide))
        = fibFSMmod3.bits k)
    ∧ (∀ k, fibFSMmod5.bits (k + fib_pisano_predict 5 (by decide))
        = fibFSMmod5.bits k)
    ∧ (∀ k, fibFSMmod7.bits (k + fib_pisano_predict 7 (by decide))
        = fibFSMmod7.bits k)
    ∧ (∀ k, fibFSMmod11.bits (k + fib_pisano_predict 11 (by decide))
        = fibFSMmod11.bits k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k; rw [fib_pisano_predict_correct.1]; exact fibFSMmod3_bits_period_8 k
  · intro k; rw [fib_pisano_predict_correct.2.1]; exact fibFSMmod5_bits_period_20 k
  · intro k; rw [fib_pisano_predict_correct.2.2.1]; exact fibFSMmod7_bits_period_16 k
  · intro k; rw [fib_pisano_predict_correct.2.2.2]; exact fibFSMmod11_bits_period_10 k

end E213.Math.Cohomology.Dyadic.Conjecture
