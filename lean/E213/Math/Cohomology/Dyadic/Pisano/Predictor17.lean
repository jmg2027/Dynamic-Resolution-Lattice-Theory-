import E213.Math.Cohomology.Dyadic.Pisano.Predictor14
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod53
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod59
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod61

import E213.Math.Cohomology.Dyadic.ArithFSM
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod11
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod13
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod17
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod19
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod23
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod29
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod31
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod37
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod41
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod43
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod47
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod5
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod7
import E213.Math.Cohomology.Dyadic.Legendre.V213
import E213.Math.Cohomology.Dyadic.Pisano.Predictor
import E213.Math.Cohomology.Dyadic.Pisano.Predictor7
/-!
# Pisano predictor — 17-prime evidence (mod 53, 59, 61 added)

  | p  | Legendre | Branch    | true bit | predict | match |
  | 53 |     2    | inert     |    54    |   54    | TIGHT | NEW
  | 59 |     1    | split     |    29    |   29    | TIGHT | NEW
  | 61 |     1    | split     |    30    |   30    | TIGHT | NEW

All three new primes TIGHT.

Inert (9): {3, 7, 13, 17, 23, 37, 43, 47, 53}
Split (7): {11, 19, 29, 31, 41, 59, 61}
Ramified (1): {5}

Total 17 primes — current strongest empirical evidence for the
Pisano predictor's universality on the Pell-5 lens.

Sub-tight cases remain at 2 of 17:
  p=29 (split, ×2): predict 14 = 2 · tight 7
  p=47 (inert, ×3): predict 48 = 3 · tight 16
-/

namespace E213.Math.Cohomology.Dyadic.Pisano.Predictor17

open E213.Math.Cohomology.Dyadic.Legendre.V213 (legendre213)
open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod17 (pellFSMmod17 pellFSMmod17_bits_period_18)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod19 (pellFSMmod19 pellFSMmod19_bits_period_9 pellFSMmod19_bits_period_18)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod23 (pellFSMmod23 pellFSMmod23_bits_period_24)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod29 (pellFSMmod29 pellFSMmod29_bits_period_14)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod31 (pellFSMmod31 pellFSMmod31_bits_period_30)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod37 (pellFSMmod37 pellFSMmod37_bits_period_38)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod41 (pellFSMmod41 pellFSMmod41_bits_period_20)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod43 (pellFSMmod43 pellFSMmod43_bits_period_44)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod47 (pellFSMmod47 pellFSMmod47_bits_period_48)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod53 (pellFSMmod53 pellFSMmod53_bits_period_54)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod59 (pellFSMmod59 pellFSMmod59_bits_period_29)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod61 (pellFSMmod61 pellFSMmod61_bits_period_30)
open E213.Math.Cohomology.Dyadic.Pisano.Predictor (pisano_predict)
open E213.Math.Cohomology.Dyadic.Pisano.Predictor7 (pisano_predict_realises_pell_7)
open E213.Math.Cohomology.Dyadic.Pisano.Predictor14 (pisano_predict_realises_pell_14)


/-- ★★★★★ Legendre 5 mod 53 = NQR (inert). -/
theorem legendre_5_mod_53 :
    legendre213 5 53 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 59 = QR (split). -/
theorem legendre_5_mod_59 :
    legendre213 5 59 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 61 = QR (split). -/
theorem legendre_5_mod_61 :
    legendre213 5 61 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 17 primes. -/
theorem pisano_predict_realises_pell_17 :
    -- All 14 previous primes
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
        = pellFSMmod37.bits k)
    ∧ (∀ k, pellFSMmod41.bits (k + pisano_predict 41 (by decide))
        = pellFSMmod41.bits k)
    ∧ (∀ k, pellFSMmod43.bits (k + pisano_predict 43 (by decide))
        = pellFSMmod43.bits k)
    ∧ (∀ k, pellFSMmod47.bits (k + pisano_predict 47 (by decide))
        = pellFSMmod47.bits k)
    -- Three new primes
    ∧ (∀ k, pellFSMmod53.bits (k + pisano_predict 53 (by decide))
        = pellFSMmod53.bits k)
    ∧ (∀ k, pellFSMmod59.bits (k + pisano_predict 59 (by decide))
        = pellFSMmod59.bits k)
    ∧ (∀ k, pellFSMmod61.bits (k + pisano_predict 61 (by decide))
        = pellFSMmod61.bits k) := by
  have h53 : pisano_predict 53 (by decide) = 54 := by decide
  have h59 : pisano_predict 59 (by decide) = 29 := by decide
  have h61 : pisano_predict 61 (by decide) = 30 := by decide
  let H := pisano_predict_realises_pell_14
  refine ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1,
          H.2.2.2.2.2.1, H.2.2.2.2.2.2.1,
          H.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.1,
          H.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.1,
          H.2.2.2.2.2.2.2.2.2.2.2.1,
          H.2.2.2.2.2.2.2.2.2.2.2.2.1,
          H.2.2.2.2.2.2.2.2.2.2.2.2.2,
          ?_, ?_, ?_⟩
  · intro k; rw [h53]; exact pellFSMmod53_bits_period_54 k
  · intro k; rw [h59]; exact pellFSMmod59_bits_period_29 k
  · intro k; rw [h61]; exact pellFSMmod61_bits_period_30 k

end E213.Math.Cohomology.Dyadic.Pisano.Predictor17
