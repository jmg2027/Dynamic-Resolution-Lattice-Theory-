import E213.Math.Cohomology.DyadicSignaturePredict

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

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★★★★ Two-layer predictor capstone: both bit and signature
    Pell periods predicted by trajectory-walking the Legendre lens. -/
theorem two_layer_predictor_capstone :
    -- Layer 1: bit-period predictor (Step 2 result)
    ((∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by omega))
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
        = pellFSMmod19.bits k))
    -- Layer 2: signature-period predictor (parity-doubled)
    ∧ ((∀ k, signature pellFSMmod3.bits (k + signature_predict 3 (by omega))
          = signature pellFSMmod3.bits k)
        ∧ (∀ k, signature pellFSMmod5.bits (k + signature_predict 5 (by omega))
          = signature pellFSMmod5.bits k)
        ∧ (∀ k, signature pellFSMmod7.bits (k + signature_predict 7 (by omega))
          = signature pellFSMmod7.bits k)
        ∧ (∀ k, signature pellFSMmod11.bits (k + signature_predict 11 (by omega))
          = signature pellFSMmod11.bits k)
        ∧ (∀ k, signature pellFSMmod13.bits (k + signature_predict 13 (by omega))
          = signature pellFSMmod13.bits k)
        ∧ (∀ k, signature pellFSMmod17.bits (k + signature_predict 17 (by omega))
          = signature pellFSMmod17.bits k)
        ∧ (∀ k, signature pellFSMmod19.bits (k + signature_predict 19 (by omega))
          = signature pellFSMmod19.bits k)) :=
  ⟨pisano_predict_realises_pell_7, signature_predict_realises_pell_7⟩

end E213.Math.Cohomology.DyadicConjecture
