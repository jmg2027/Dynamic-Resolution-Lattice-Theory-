import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Legendre
import E213.Lib.Math.DyadicFSM.TwoLayerPredictor

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.Pisano.Predictor
import E213.Lib.Math.DyadicFSM.Pisano.Predictor7
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

namespace E213.Lib.Math.DyadicFSM.Pisano.Predictor8

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod17 (pellFSMmod17 pellFSMmod17_bits_period_18)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod19 (pellFSMmod19 pellFSMmod19_bits_period_9 pellFSMmod19_bits_period_18)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod23 (pellFSMmod23 pellFSMmod23_bits_period_24)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor (pisano_predict)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor7 (pisano_predict_realises_pell_7)


/-- ★★★★★ Legendre 5 mod 23 = NQR (inert). -/
theorem legendre_5_mod_23 :
    legendre213 5 23 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor computes Pell period at 8 primes. -/
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

end E213.Lib.Math.DyadicFSM.Pisano.Predictor8
