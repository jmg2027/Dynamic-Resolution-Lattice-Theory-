import E213.Lib.Math.DyadicFSM.Fib.FSMmod
import E213.Lib.Math.DyadicFSM.Fib.PisanoCapstone

import E213.Lib.Math.DyadicFSM.Legendre.V213
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

namespace E213.Lib.Math.DyadicFSM.Fib.Pisano8

open E213.Lib.Math.DyadicFSM.Fib.FSMmod3 (fibFSMmod3 fibFSMmod3_bits_period_8)
open E213.Lib.Math.DyadicFSM.Fib.PisanoCapstone (fib_pisano_predict fib_pisano_predict_realises)
open E213.Lib.Math.DyadicFSM.Fib.FSMmod5 (fibFSMmod5 fibFSMmod5_bits_period_20)
open E213.Lib.Math.DyadicFSM.Fib.FSMmod7 (fibFSMmod7 fibFSMmod7_bits_period_16)
open E213.Lib.Math.DyadicFSM.Fib.FSMmod11 (fibFSMmod11 fibFSMmod11_bits_period_10)
open E213.Lib.Math.DyadicFSM.Fib.FSMmod17 (fibFSMmod17 fibFSMmod17_bits_period_36)
open E213.Lib.Math.DyadicFSM.Fib.FSMmod19 (fibFSMmod19 fibFSMmod19_bits_period_18)
open E213.Lib.Math.DyadicFSM.Fib.FSMmod13 (fibFSMmod13 fibFSMmod13_bits_period_28)
open E213.Lib.Math.DyadicFSM.Fib.FSMmod23 (fibFSMmod23 fibFSMmod23_bits_period_48)
open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)


/-- ★★★★★ Legendre 5 mod 13 = NQR (inert). -/
theorem fib_legendre_5_mod_13 :
    legendre213 5 13 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 17 = NQR (inert). -/
theorem fib_legendre_5_mod_17 :
    legendre213 5 17 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 19 = QR (split). -/
theorem fib_legendre_5_mod_19 :
    legendre213 5 19 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 23 = NQR (inert). -/
theorem fib_legendre_5_mod_23 :
    legendre213 5 23 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Fibonacci predictor REALISES Pell period at 8 primes. -/
theorem fib_pisano_predict_realises_8 :
    (∀ k, fibFSMmod3.bits (k + fib_pisano_predict 3 (by decide))
        = fibFSMmod3.bits k)
    ∧ (∀ k, fibFSMmod5.bits (k + fib_pisano_predict 5 (by decide))
        = fibFSMmod5.bits k)
    ∧ (∀ k, fibFSMmod7.bits (k + fib_pisano_predict 7 (by decide))
        = fibFSMmod7.bits k)
    ∧ (∀ k, fibFSMmod11.bits (k + fib_pisano_predict 11 (by decide))
        = fibFSMmod11.bits k)
    ∧ (∀ k, fibFSMmod13.bits (k + fib_pisano_predict 13 (by decide))
        = fibFSMmod13.bits k)
    ∧ (∀ k, fibFSMmod17.bits (k + fib_pisano_predict 17 (by decide))
        = fibFSMmod17.bits k)
    ∧ (∀ k, fibFSMmod19.bits (k + fib_pisano_predict 19 (by decide))
        = fibFSMmod19.bits k)
    ∧ (∀ k, fibFSMmod23.bits (k + fib_pisano_predict 23 (by decide))
        = fibFSMmod23.bits k) := by
  have h13 : fib_pisano_predict 13 (by decide) = 28 := by decide
  have h17 : fib_pisano_predict 17 (by decide) = 36 := by decide
  have h19 : fib_pisano_predict 19 (by decide) = 18 := by decide
  have h23 : fib_pisano_predict 23 (by decide) = 48 := by decide
  refine ⟨fib_pisano_predict_realises.1,
          fib_pisano_predict_realises.2.1,
          fib_pisano_predict_realises.2.2.1,
          fib_pisano_predict_realises.2.2.2,
          ?_, ?_, ?_, ?_⟩
  · intro k; rw [h13]; exact fibFSMmod13_bits_period_28 k
  · intro k; rw [h17]; exact fibFSMmod17_bits_period_36 k
  · intro k; rw [h19]; exact fibFSMmod19_bits_period_18 k
  · intro k; rw [h23]; exact fibFSMmod23_bits_period_48 k

end E213.Lib.Math.DyadicFSM.Fib.Pisano8
