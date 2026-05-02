import E213.Math.Cohomology.Dyadic.TwoLayerPredictor
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod23

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

namespace E213.Math.Cohomology.Dyadic.Pisano.Predictor8

open E213.Math.Cohomology.Dyadic.Legendre.V213 (legendre213)
open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5)


/-- ★★★★★ Legendre 5 mod 23 = NQR (inert). -/
theorem legendre_5_mod_23 :
    legendre213 5 23 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 8 primes. -/
theorem pisano_predict_realises_pell_8 :
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
        = pellFSMmod19.bits k)
    ∧ (∀ k, pellFSMmod23.bits (k + pisano_predict 23 (by decide))
        = pellFSMmod23.bits k) := by
  have h23 : pisano_predict 23 (by decide) = 24 := by decide
  refine ⟨pisano_predict_realises_pell_7.1,
          pisano_predict_realises_pell_7.2.1,
          pisano_predict_realises_pell_7.2.2.1,
          pisano_predict_realises_pell_7.2.2.2.1,
          pisano_predict_realises_pell_7.2.2.2.2.1,
          pisano_predict_realises_pell_7.2.2.2.2.2.1,
          pisano_predict_realises_pell_7.2.2.2.2.2.2,
          ?_⟩
  intro k; rw [h23]; exact pellFSMmod23_bits_period_24 k

end E213.Math.Cohomology.Dyadic.Pisano.Predictor8
