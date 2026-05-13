import E213.Lib.Math.DyadicFSM.ArithFSM.ModMedium
import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Legendre.Legendre
import E213.Lib.Math.DyadicFSM.Pisano.Predictor8

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.Pisano.Predictor
import E213.Lib.Math.DyadicFSM.Pisano.Predictor7
/-!
# Pisano predictor — 11-prime evidence (mod 29, 31, 37 added)

  | p  | Legendre | Branch    | bit | sig | predict (bit/sig) |
  |  3 |     2    | inert     |  4  |  4  |    4 / 4         |
  |  5 |     0    | ramified  | 10  | 10  |   10 / 10        |
  |  7 |     2    | inert     |  8  |  8  |    8 / 8         |
  | 11 |     1    | split     |  5  | 10  |    5 / 10        |
  | 13 |     2    | inert     | 14  | 14  |   14 / 14        |
  | 17 |     2    | inert     | 18  | 18  |   18 / 18        |
  | 19 |     1    | split     |  9  | 18  |    9 / 18        |
  | 23 |     2    | inert     | 24  | 24  |   24 / 24        |
  | 29 |     1    | split     |  7  | 14  |   14 / 14   NEW  |
  | 31 |     1    | split     | 15  | 30  |   15 / 30   NEW  |
  | 37 |     2    | inert     | 38  | 38  |   38 / 38   NEW  |

Inert verified at 6 sizes: {3, 7, 13, 17, 23, 37}.
Split verified at 4 sizes: {11, 19, 29, 31}.
Ramified verified at 1 size: {5}.

Total 11 primes — strongest empirical evidence yet for the Pisano
predictor's universality on the Pell-5 lens.

Note: at p=29 the predicted period 14 = (p-1)/2 is *not* tight —
true period is 7 (a divisor).  predicted = 2 · tight, so bits cycle
with both periods.  Predictor gives an upper bound on the true
bit-period, not necessarily tight in the split branch.
-/

namespace E213.Lib.Math.DyadicFSM.Pisano.Predictor11

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod17 (pellFSMmod17 pellFSMmod17_bits_period_18)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod19 (pellFSMmod19 pellFSMmod19_bits_period_9 pellFSMmod19_bits_period_18)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod23 (pellFSMmod23 pellFSMmod23_bits_period_24)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod29 (pellFSMmod29 pellFSMmod29_bits_period_14)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod31 (pellFSMmod31 pellFSMmod31_bits_period_15 pellFSMmod31_bits_period_30)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod37 (pellFSMmod37 pellFSMmod37_bits_period_38)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor (pisano_predict)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor7 (pisano_predict_realises_pell_7)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor8 (pisano_predict_realises_pell_8)


/-- ★★★★★ Legendre 5 mod 29 = QR (split). -/
theorem legendre_5_mod_29 :
    legendre213 5 29 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 31 = QR (split). -/
theorem legendre_5_mod_31 :
    legendre213 5 31 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 37 = NQR (inert). -/
theorem legendre_5_mod_37 :
    legendre213 5 37 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 11 primes.

  Extends the 8-prime evidence (`pisano_predict_realises_pell_8`) by
  adding mod 29, 31, 37.  At each new prime, the Legendre-driven
  predictor formula (split→(p-1)/2, inert→p+1) yields a period N
  satisfying  ∀ k, bits(k + N) = bits(k). -/
theorem pisano_predict_realises_pell_11 :
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
        = pellFSMmod23.bits k)
    ∧ (∀ k, pellFSMmod29.bits (k + pisano_predict 29 (by decide))
        = pellFSMmod29.bits k)
    ∧ (∀ k, pellFSMmod31.bits (k + pisano_predict 31 (by decide))
        = pellFSMmod31.bits k)
    ∧ (∀ k, pellFSMmod37.bits (k + pisano_predict 37 (by decide))
        = pellFSMmod37.bits k) := by
  have h29 : pisano_predict 29 (by decide) = 14 := by decide
  have h31 : pisano_predict 31 (by decide) = 15 := by decide
  have h37 : pisano_predict 37 (by decide) = 38 := by decide
  refine ⟨pisano_predict_realises_pell_8.1,
          pisano_predict_realises_pell_8.2.1,
          pisano_predict_realises_pell_8.2.2.1,
          pisano_predict_realises_pell_8.2.2.2.1,
          pisano_predict_realises_pell_8.2.2.2.2.1,
          pisano_predict_realises_pell_8.2.2.2.2.2.1,
          pisano_predict_realises_pell_8.2.2.2.2.2.2.1,
          pisano_predict_realises_pell_8.2.2.2.2.2.2.2,
          ?_, ?_, ?_⟩
  · intro k; rw [h29]; exact pellFSMmod29_bits_period_14 k
  · intro k; rw [h31]; exact pellFSMmod31_bits_period_15 k
  · intro k; rw [h37]; exact pellFSMmod37_bits_period_38 k

end E213.Lib.Math.DyadicFSM.Pisano.Predictor11
