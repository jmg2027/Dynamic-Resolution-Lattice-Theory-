import E213.Math.Cohomology.Dyadic.Pisano.Predictor6
import E213.Math.Cohomology.Dyadic.ArithFSMmod17

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

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★ Legendre 5 mod 17 = NQR (inert). -/
theorem legendre_5_mod_17 :
    legendre213 5 17 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Predictor REALISES Pell period at all 7 verified primes. -/
theorem pisano_predict_realises_pell_7 :
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
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide))
        = pellFSMmod17.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by decide))
        = pellFSMmod19.bits k) := by
  have h17 : pisano_predict 17 (by decide) = 18 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro k; rw [h17]; exact pellFSMmod17_bits_period_18 k
  · intro k; rw [pisano_predict_correct_6.2.2.2.2.2]
    exact pellFSMmod19_bits_period_9 k

end E213.Math.Cohomology.Dyadic.Conjecture
