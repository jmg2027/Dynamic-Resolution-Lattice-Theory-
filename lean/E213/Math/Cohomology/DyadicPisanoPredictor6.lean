import E213.Math.Cohomology.DyadicPisanoPredictor
import E213.Math.Cohomology.DyadicLegendre13_19

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

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★★ Predictor matches concrete period at extended primes. -/
theorem pisano_predict_correct_6 :
    pisano_predict 3 (by omega) = 4
    ∧ pisano_predict 5 (by omega) = 10
    ∧ pisano_predict 7 (by omega) = 8
    ∧ pisano_predict 11 (by omega) = 5
    ∧ pisano_predict 13 (by omega) = 14
    ∧ pisano_predict 19 (by omega) = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ Predictor REALISES Pell period at all 6 verified primes. -/
theorem pisano_predict_realises_pell_6 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by omega))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by omega))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by omega))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by omega))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by omega))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by omega))
        = pellFSMmod19.bits k) := by
  obtain ⟨h3, h5, h7, h11, h13, h19⟩ := pisano_predict_correct_6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; rw [h3]; exact pellFSMmod3_bits_period_4 k
  · intro k; rw [h5]; exact pellFSMmod5_bits_period_10 k
  · intro k; rw [h7]; exact pellFSMmod7_bits_period_8 k
  · intro k; rw [h11]; exact pellFSMmod11_bits_period_5 k
  · intro k; rw [h13]; exact pellFSMmod13_bits_period_14 k
  · intro k; rw [h19]; exact pellFSMmod19_bits_period_9 k

end E213.Math.Cohomology.DyadicConjecture
