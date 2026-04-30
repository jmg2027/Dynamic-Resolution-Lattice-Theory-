import E213.Math.Cohomology.DyadicTwoLayerPredictor
import E213.Math.Cohomology.DyadicArithFSMmod23

/-!
# Pisano predictor — 8-prime evidence + signature layer

  | p  | Legendre | Branch    | bit | sig | predict (bit/sig) |
  |  3 |     2    | inert     |  4  |  4  |    4 / 4         |
  |  5 |     0    | ramified  | 10  | 10  |   10 / 10        |
  |  7 |     2    | inert     |  8  |  8  |    8 / 8         |
  | 11 |     1    | split     |  5  | 10  |    5 / 10        |
  | 13 |     2    | inert     | 14  | 14  |   14 / 14        |
  | 17 |     2    | inert     | 18  | 18  |   18 / 18        |
  | 19 |     1    | split     |  9  | 18  |    9 / 18        |
  | 23 |     2    | inert     | 24  | 24  |   24 / 24        |  NEW

Inert verified at 5 sizes (p+1 formula): 3, 7, 13, 17, 23.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★ Legendre 5 mod 23 = NQR (inert). -/
theorem legendre_5_mod_23 :
    legendre213 5 23 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 8 primes. -/
theorem pisano_predict_realises_pell_8 :
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
        = pellFSMmod19.bits k)
    ∧ (∀ k, pellFSMmod23.bits (k + pisano_predict 23 (by omega))
        = pellFSMmod23.bits k) := by
  have h23 : pisano_predict 23 (by omega) = 24 := by decide
  obtain ⟨h3, h5, h7, h11, h13, h17, h19⟩ := pisano_predict_realises_pell_7
  refine ⟨h3, h5, h7, h11, h13, h17, h19, ?_⟩
  intro k; rw [h23]; exact pellFSMmod23_bits_period_24 k

end E213.Math.Cohomology.DyadicConjecture
