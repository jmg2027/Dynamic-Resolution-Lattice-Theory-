import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Signature.SignaturePredict

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.Pisano.Predictor
import E213.Lib.Math.DyadicFSM.Pisano.PredictorChain
import E213.Lib.Math.DyadicFSM.Signature.Signature
/-!
# Two-layer predictor capstone

Bundles the two trajectory-walking predictors into a single
2-conjunct theorem covering both lens layers:

  Layer 1 (bit-stream): `pisano_predict p`
    Reads Legendre lens terminal → predicts bit period.

  Layer 2 (signature):  `signature_predict p = parity-double-of-Layer-1`
    Adds K_{3,2}^{(2)} bipartite parity coupling.

Both predictors REALISE actual periods at all 7 verified primes.
This is the operational form of "Pisano CRT lifted through the
K_{3,2}^{(2)} signature lens".
-/

namespace E213.Lib.Math.DyadicFSM.TwoLayerPredictor
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod17 (pellFSMmod17 pellFSMmod17_bits_period_18)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod19 (pellFSMmod19 pellFSMmod19_bits_period_9)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor (pisano_predict)
open E213.Lib.Math.DyadicFSM.Pisano.PredictorChain (pisano_predict_realises_pell_7)
open E213.Lib.Math.DyadicFSM.Signature.SignaturePredict (signature_predict_realises_pell_7 signature_predict)

open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5)


/-- ★★★★★★★★ Two-layer predictor capstone: both bit and signature
    Pell periods predicted by trajectory-walking the Legendre lens. -/
theorem two_layer_predictor_capstone :
    -- Layer 1: bit-period predictor (Step 2 result)
    ((∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
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
        = pellFSMmod19.bits k))
    -- Layer 2: signature-period predictor (parity-doubled)
    ∧ ((∀ k, signature pellFSMmod3.bits (k + signature_predict 3 (by decide))
          = signature pellFSMmod3.bits k)
        ∧ (∀ k, signature pellFSMmod5.bits (k + signature_predict 5 (by decide))
          = signature pellFSMmod5.bits k)
        ∧ (∀ k, signature pellFSMmod7.bits (k + signature_predict 7 (by decide))
          = signature pellFSMmod7.bits k)
        ∧ (∀ k, signature pellFSMmod11.bits (k + signature_predict 11 (by decide))
          = signature pellFSMmod11.bits k)
        ∧ (∀ k, signature pellFSMmod13.bits (k + signature_predict 13 (by decide))
          = signature pellFSMmod13.bits k)
        ∧ (∀ k, signature pellFSMmod17.bits (k + signature_predict 17 (by decide))
          = signature pellFSMmod17.bits k)
        ∧ (∀ k, signature pellFSMmod19.bits (k + signature_predict 19 (by decide))
          = signature pellFSMmod19.bits k)) :=
  ⟨pisano_predict_realises_pell_7, signature_predict_realises_pell_7⟩

end E213.Lib.Math.DyadicFSM.TwoLayerPredictor
