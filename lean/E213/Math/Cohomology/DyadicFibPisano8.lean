import E213.Math.Cohomology.DyadicFibPisanoCapstone
import E213.Math.Cohomology.DyadicFibFSMmod13
import E213.Math.Cohomology.DyadicFibFSMmod17
import E213.Math.Cohomology.DyadicFibFSMmod19
import E213.Math.Cohomology.DyadicFibFSMmod23

/-!
# Fibonacci-Pisano predictor — 8-prime evidence (mod 13, 17, 19, 23 added)

  | p  | Legendre | Branch    | π(p) | predict | match |
  |  3 |     2    | inert     |   8  |    8    | TIGHT |
  |  5 |     0    | ramified  |  20  |   20    | TIGHT |
  |  7 |     2    | inert     |  16  |   16    | TIGHT |
  | 11 |     1    | split     |  10  |   10    | TIGHT |
  | 13 |     2    | inert     |  28  |   28    | TIGHT | NEW
  | 17 |     2    | inert     |  36  |   36    | TIGHT | NEW
  | 19 |     1    | split     |  18  |   18    | TIGHT | NEW
  | 23 |     2    | inert     |  48  |   48    | TIGHT | NEW

All 8 TIGHT.  Coverage:
  Inert (5): {3, 7, 13, 17, 23}
  Split (2): {11, 19}
  Ramified (1): {5}

Matches the original Pell 8-prime baseline (commit f8a5ca8) at the
same prime set, with predictor formula 2× scaled (cross-recurrence
relation, commit 35bef8d).
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★ Legendre 5 mod 13 = NQR (inert). -/
theorem fib_legendre_5_mod_13 :
    legendre213 5 13 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 17 = NQR (inert). -/
theorem fib_legendre_5_mod_17 :
    legendre213 5 17 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 19 = QR (split). -/
theorem fib_legendre_5_mod_19 :
    legendre213 5 19 (by omega) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 23 = NQR (inert). -/
theorem fib_legendre_5_mod_23 :
    legendre213 5 23 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Fibonacci predictor REALISES Pell period at 8 primes. -/
theorem fib_pisano_predict_realises_8 :
    (∀ k, fibFSMmod3.bits (k + fib_pisano_predict 3 (by omega))
        = fibFSMmod3.bits k)
    ∧ (∀ k, fibFSMmod5.bits (k + fib_pisano_predict 5 (by omega))
        = fibFSMmod5.bits k)
    ∧ (∀ k, fibFSMmod7.bits (k + fib_pisano_predict 7 (by omega))
        = fibFSMmod7.bits k)
    ∧ (∀ k, fibFSMmod11.bits (k + fib_pisano_predict 11 (by omega))
        = fibFSMmod11.bits k)
    ∧ (∀ k, fibFSMmod13.bits (k + fib_pisano_predict 13 (by omega))
        = fibFSMmod13.bits k)
    ∧ (∀ k, fibFSMmod17.bits (k + fib_pisano_predict 17 (by omega))
        = fibFSMmod17.bits k)
    ∧ (∀ k, fibFSMmod19.bits (k + fib_pisano_predict 19 (by omega))
        = fibFSMmod19.bits k)
    ∧ (∀ k, fibFSMmod23.bits (k + fib_pisano_predict 23 (by omega))
        = fibFSMmod23.bits k) := by
  have h13 : fib_pisano_predict 13 (by omega) = 28 := by decide
  have h17 : fib_pisano_predict 17 (by omega) = 36 := by decide
  have h19 : fib_pisano_predict 19 (by omega) = 18 := by decide
  have h23 : fib_pisano_predict 23 (by omega) = 48 := by decide
  obtain ⟨h3, h5, h7, h11⟩ := fib_pisano_predict_realises
  refine ⟨h3, h5, h7, h11, ?_, ?_, ?_, ?_⟩
  · intro k; rw [h13]; exact fibFSMmod13_bits_period_28 k
  · intro k; rw [h17]; exact fibFSMmod17_bits_period_36 k
  · intro k; rw [h19]; exact fibFSMmod19_bits_period_18 k
  · intro k; rw [h23]; exact fibFSMmod23_bits_period_48 k

end E213.Math.Cohomology.DyadicConjecture
