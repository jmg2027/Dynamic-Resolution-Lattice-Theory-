import E213.Lib.Math.DyadicFSM.ArithFSM.ModLarge
import E213.Lib.Math.DyadicFSM.ArithFSM.ModMedium
import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Legendre
import E213.Lib.Math.DyadicFSM.Pisano.Predictor17

/-!
# Pisano predictor — 20-prime evidence (mod 67, 71, 73 added)

  | p  | Legendre | Branch    | π(p) | predict | match |
  | 67 |     2    | inert     |  68  |   68    | TIGHT | NEW
  | 71 |     1    | split     |  35  |   35    | TIGHT | NEW
  | 73 |     2    | inert     |  74  |   74    | TIGHT | NEW

All 3 new TIGHT.

Coverage:
  Inert (10): {3, 7, 13, 17, 23, 37, 43, 47, 53, 67, 73} — wait that's 11
  Split (8): {11, 19, 29, 31, 41, 59, 61, 71}
  Ramified (1): {5}

Sub-tight cases at 2 of 20:
  p=29 (split, ×2): predict 14 = 2 · tight 7
  p=47 (inert, ×3): predict 48 = 3 · tight 16

These 2 sub-tight remain isolated up to p=73.
-/

namespace E213.Lib.Math.DyadicFSM.Pisano.Predictor20

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod2)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod11 (pellFSMmod11)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod13 (pellFSMmod13)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod17 (pellFSMmod17)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod19 (pellFSMmod19)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod23 (pellFSMmod23)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod29 (pellFSMmod29)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod31 (pellFSMmod31)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod37 (pellFSMmod37)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod41 (pellFSMmod41)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod43 (pellFSMmod43)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod47 (pellFSMmod47)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod53 (pellFSMmod53 pellFSMmod53_bits_period_54)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod59 (pellFSMmod59 pellFSMmod59_bits_period_29)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod61 (pellFSMmod61 pellFSMmod61_bits_period_30)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod67 (pellFSMmod67 pellFSMmod67_bits_period_68)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod71 (pellFSMmod71 pellFSMmod71_bits_period_35)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod73 (pellFSMmod73 pellFSMmod73_bits_period_74)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor (pisano_predict pisano_period_lift)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor17 (pisano_predict_realises_pell_17)

theorem legendre_5_mod_67 :
    legendre213 5 67 (by decide) = ⟨2, by decide⟩ := by decide

theorem legendre_5_mod_71 :
    legendre213 5 71 (by decide) = ⟨1, by decide⟩ := by decide

theorem legendre_5_mod_73 :
    legendre213 5 73 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor computes Pell period at 20 primes.
    Extends 17-prime chain with mod 67, 71, 73. -/
theorem pisano_predict_realises_pell_20 :
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
    ∧ (∀ k, pellFSMmod53.bits (k + pisano_predict 53 (by decide))
        = pellFSMmod53.bits k)
    ∧ (∀ k, pellFSMmod59.bits (k + pisano_predict 59 (by decide))
        = pellFSMmod59.bits k)
    ∧ (∀ k, pellFSMmod61.bits (k + pisano_predict 61 (by decide))
        = pellFSMmod61.bits k)
    ∧ (∀ k, pellFSMmod67.bits (k + pisano_predict 67 (by decide))
        = pellFSMmod67.bits k)
    ∧ (∀ k, pellFSMmod71.bits (k + pisano_predict 71 (by decide))
        = pellFSMmod71.bits k)
    ∧ (∀ k, pellFSMmod73.bits (k + pisano_predict 73 (by decide))
        = pellFSMmod73.bits k) := by
  let H := pisano_predict_realises_pell_17
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1,
         H.2.2.2.2.2.1, H.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
         pisano_period_lift (by decide : pisano_predict 67 (by decide) = 68)
                            pellFSMmod67_bits_period_68,
         pisano_period_lift (by decide : pisano_predict 71 (by decide) = 35)
                            pellFSMmod71_bits_period_35,
         pisano_period_lift (by decide : pisano_predict 73 (by decide) = 74)
                            pellFSMmod73_bits_period_74⟩

end E213.Lib.Math.DyadicFSM.Pisano.Predictor20
