import E213.Math.Cohomology.DyadicPisanoPredictor6
import E213.Math.Cohomology.DyadicArithFSMmod17

/-!
# Pisano predictor — extended to 7 primes (adding p=17)

  | p  | Legendre | Branch    | TIGHT period | predict(p) |
  |  3 | 2 (NQR)  | inert     |     4        |     4      |
  |  5 | 0        | ramified  |    10        |    10      |
  |  7 | 2 (NQR)  | inert     |     8        |     8      |
  | 11 | 1 (QR)   | split     |     5        |     5      |
  | 13 | 2 (NQR)  | inert     |    14        |    14      |
  | 17 | 2 (NQR)  | inert     |    18        |    18      |  NEW
  | 19 | 1 (QR)   | split     |     9        |     9      |

7 of 7 primes verified.  All <= {propext, Quot.sound}.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★ Legendre 5 mod 17 = NQR (inert). -/
theorem legendre_5_mod_17 :
    legendre213 5 17 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Predictor REALISES Pell period at all 7 verified primes. -/
theorem pisano_predict_realises_pell_7 :
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
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by omega))
        = pellFSMmod17.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by omega))
        = pellFSMmod19.bits k) := by
  have h17 : pisano_predict 17 (by omega) = 18 := by decide
  obtain ⟨h3, h5, h7, h11, h13, h19⟩ := pisano_predict_correct_6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; rw [h3]; exact pellFSMmod3_bits_period_4 k
  · intro k; rw [h5]; exact pellFSMmod5_bits_period_10 k
  · intro k; rw [h7]; exact pellFSMmod7_bits_period_8 k
  · intro k; rw [h11]; exact pellFSMmod11_bits_period_5 k
  · intro k; rw [h13]; exact pellFSMmod13_bits_period_14 k
  · intro k; rw [h17]; exact pellFSMmod17_bits_period_18 k
  · intro k; rw [h19]; exact pellFSMmod19_bits_period_9 k

end E213.Math.Cohomology.DyadicConjecture
