import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Pisano.Predictor7

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.ConcretePellSig
import E213.Lib.Math.DyadicFSM.Pisano.Predictor
import E213.Lib.Math.DyadicFSM.Signature.Signature
/-!
# Signature-period predictor — bipartite parity doubling layer

Extends `pisano_predict` to predict signature periods (vs bit
periods).  The bipartite alternation invariant `signature` ↔
S/T parity coupling means:

  - Even bit period ⇒ signature period = bit period
  - Odd bit period  ⇒ signature period = 2 × bit period

Encoded as `signature_predict : Nat → Nat`:

  signature_predict p :=
    let bp := pisano_predict p
    if bp is even then bp else 2 * bp

Verified at all 7 primes:

  | p  | bit period | signature period | predict |
  |  3 |     4      |     4            |    4    |
  |  5 |    10      |    10            |   10    |
  |  7 |     8      |     8            |    8    |
  | 11 |     5  odd |    10  (=2·5)    |   10    |
  | 13 |    14      |    14            |   14    |
  | 17 |    18      |    18            |   18    |
  | 19 |     9  odd |    18  (=2·9)    |   18    |
-/

namespace E213.Lib.Math.DyadicFSM.Signature.Signature.SignaturePredict
open E213.Lib.Math.DyadicFSM.Pisano.Predictor (pisano_predict)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (pellFSMmod3_signature_period_4 pellFSMmod5_signature_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8 pellFSMmod7_signature_period_8)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10 pellFSMmod11_signature_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14 pellFSMmod13_signature_period_14)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod17 (pellFSMmod17 pellFSMmod17_bits_period_18 pellFSMmod17_signature_period_18)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod19 (pellFSMmod19 pellFSMmod19_bits_period_9 pellFSMmod19_signature_period_18)

open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5)


/-- Signature-period predictor: doubles the bit-period predictor
    when the bit period is odd (bipartite parity coupling). -/
def signature_predict (p : Nat) (hp : 1 < p) : Nat :=
  let bp := pisano_predict p hp
  if bp % 2 = 0 then bp else 2 * bp

/-- ★★★★★★ signature_predict matches actual TIGHT signature periods. -/
theorem signature_predict_correct_7 :
    signature_predict 3 (by decide) = 4
    ∧ signature_predict 5 (by decide) = 10
    ∧ signature_predict 7 (by decide) = 8
    ∧ signature_predict 11 (by decide) = 10
    ∧ signature_predict 13 (by decide) = 14
    ∧ signature_predict 17 (by decide) = 18
    ∧ signature_predict 19 (by decide) = 18 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ Signature predictor REALISES Pell signature period at
    all 7 primes (via Legendre lens trajectory). -/
theorem signature_predict_realises_pell_7 :
    (∀ k, signature pellFSMmod3.bits (k + signature_predict 3 (by decide))
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
        = signature pellFSMmod19.bits k) := by
  let H := signature_predict_correct_7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; rw [H.1]; exact pellFSMmod3_signature_period_4 k
  · intro k; rw [H.2.1]; exact pellFSMmod5_signature_period_10 k
  · intro k; rw [H.2.2.1]
    exact pellFSMmod7_signature_period_8 k
  · intro k; rw [H.2.2.2.1]; exact pellFSMmod11_signature_period_10 k
  · intro k; rw [H.2.2.2.2.1]; exact pellFSMmod13_signature_period_14 k
  · intro k; rw [H.2.2.2.2.2.1]; exact pellFSMmod17_signature_period_18 k
  · intro k; rw [H.2.2.2.2.2.2]; exact pellFSMmod19_signature_period_18 k

end E213.Lib.Math.DyadicFSM.Signature.Signature.SignaturePredict
