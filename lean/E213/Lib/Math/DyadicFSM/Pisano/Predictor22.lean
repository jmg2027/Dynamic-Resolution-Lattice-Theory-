import E213.Lib.Math.DyadicFSM.ArithFSM.ModLarge
import E213.Lib.Math.DyadicFSM.ArithFSM.ModMedium
import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Legendre
import E213.Lib.Math.DyadicFSM.Pisano.Predictor20

/-!
# Pisano predictor — 22-prime evidence + sub-tight pattern

Extends 20-prime Pell-5 predictor (commit 81919aa) to 22 primes.

  | p  | leg | branch | tight | predict | match  |
  | 79 |  1  | split  |  39   |   39    | TIGHT  |
  | 89 |  1  | split  |  22   |   44    | ×2 SUB |  ← NEW

★ Third ×2 sub-tight case (after p=29, p=47) ★

Sub-tight history (3 of 22):
  p=29 (split, ×2): tight 7,  predict 14
  p=47 (inert, ×3): tight 16, predict 48
  p=89 (split, ×2): tight 22, predict 44

Pattern: split ×2 sub-tight at p ∈ {29, 89, 101, ...}
        inert ×3 sub-tight at p ∈ {47, ...}

Frobenius-orbit interpretation: predictor is upper bound, tight
period coincides iff no Frobenius-stable proper subgroup.
-/

namespace E213.Lib.Math.DyadicFSM.Pisano.Predictor22

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
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod53 (pellFSMmod53)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod59 (pellFSMmod59)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod61 (pellFSMmod61)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod67 (pellFSMmod67)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod71 (pellFSMmod71)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod73 (pellFSMmod73)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod79 (pellFSMmod79 pellFSMmod79_bits_period_39)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod89 (pellFSMmod89 pellFSMmod89_bits_period_44)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor (pisano_predict pisano_period_lift)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor20 (pisano_predict_realises_pell_20)

theorem legendre_5_mod_79 :
    legendre213 5 79 (by decide) = ⟨1, by decide⟩ := by decide

theorem legendre_5_mod_89 :
    legendre213 5 89 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor computes Pell period at 22 primes.
    Extends 20-prime chain with mod 79, 89.  Sub-tight ×2 at p=89.

    Sub-tight history (3 of 22):
      p=29 (split, ×2): predict 14 = 2 · tight 7
      p=47 (inert, ×3): predict 48 = 3 · tight 16
      p=89 (split, ×2): predict 44 = 2 · tight 22

    The predictor remains a VALID period at sub-tight primes
    (period_44 used for p=89, even though tight is 22). -/
theorem pisano_predict_realises_pell_22 :
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
        = pellFSMmod73.bits k)
    ∧ (∀ k, pellFSMmod79.bits (k + pisano_predict 79 (by decide))
        = pellFSMmod79.bits k)
    ∧ (∀ k, pellFSMmod89.bits (k + pisano_predict 89 (by decide))
        = pellFSMmod89.bits k) := by
  let H := pisano_predict_realises_pell_20
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1,
         H.2.2.2.2.2.1, H.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
         pisano_period_lift (by decide : pisano_predict 79 (by decide) = 39)
                            pellFSMmod79_bits_period_39,
         pisano_period_lift (by decide : pisano_predict 89 (by decide) = 44)
                            pellFSMmod89_bits_period_44⟩

end E213.Lib.Math.DyadicFSM.Pisano.Predictor22
