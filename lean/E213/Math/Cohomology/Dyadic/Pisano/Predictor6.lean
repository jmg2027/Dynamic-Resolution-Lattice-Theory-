import E213.Math.Cohomology.Dyadic.Pisano.Predictor
import E213.Math.Cohomology.Dyadic.Legendre.V13_19

/-!
# Pisano predictor — extended to 6 primes

The trajectory-walking predictor `pisano_predict` correctly
computes the period for all 6 verified primes:

  | p  | predict(p) | TIGHT period | Match |
  |  3 |     4      |     4        |  ✓    |
  |  5 |    10      |    10        |  ✓    |
  |  7 |     8      |     8        |  ✓    |
  | 11 |     5      |     5        |  ✓    |
  | 13 |    14      |    14        |  ✓    |
  | 19 |     9      |     9        |  ✓    |

100% match across split, inert, and ramified branches.
-/

namespace E213.Math.Cohomology.Dyadic.Pisano.Predictor6

open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod17 (pellFSMmod17 pellFSMmod17_bits_period_18)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod19 (pellFSMmod19 pellFSMmod19_bits_period_9)
open E213.Math.Cohomology.Dyadic.Pisano.Predictor (pisano_predict)


/-- ★★★★★★ Predictor matches concrete period at extended primes. -/
theorem pisano_predict_correct_6 :
    pisano_predict 3 (by decide) = 4
    ∧ pisano_predict 5 (by decide) = 10
    ∧ pisano_predict 7 (by decide) = 8
    ∧ pisano_predict 11 (by decide) = 5
    ∧ pisano_predict 13 (by decide) = 14
    ∧ pisano_predict 19 (by decide) = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ Predictor REALISES Pell period at all 6 verified primes. -/
theorem pisano_predict_realises_pell_6 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by decide))
        = pellFSMmod19.bits k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; rw [pisano_predict_correct_6.1]
    exact pellFSMmod3_bits_period_4 k
  · intro k; rw [pisano_predict_correct_6.2.1]
    exact pellFSMmod5_bits_period_10 k
  · intro k; rw [pisano_predict_correct_6.2.2.1]
    exact pellFSMmod7_bits_period_8 k
  · intro k; rw [pisano_predict_correct_6.2.2.2.1]
    exact pellFSMmod11_bits_period_5 k
  · intro k; rw [pisano_predict_correct_6.2.2.2.2.1]
    exact pellFSMmod13_bits_period_14 k
  · intro k; rw [pisano_predict_correct_6.2.2.2.2.2]
    exact pellFSMmod19_bits_period_9 k

end E213.Math.Cohomology.Dyadic.Pisano.Predictor6
