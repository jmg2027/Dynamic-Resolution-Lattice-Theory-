import E213.Math.Cohomology.Dyadic.Pell.Lens

import E213.Math.Cohomology.Dyadic.ArithFSM
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod5
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod7
import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.BitFSM
import E213.Math.Cohomology.Dyadic.ProductFSM
import E213.Math.Cohomology.Dyadic.ProductFSMPeriod
import E213.Math.Cohomology.Dyadic.ProductFSMPeriodDvd
/-!
# Pell lens — all pairwise compositions

Extends `pellLens_3x5_period_20` to the remaining pairs:
  - mod 3 × mod 7: lcm(4, 8) = 8
  - mod 5 × mod 7: lcm(10, 8) = 40
-/

namespace E213.Math.Cohomology.Dyadic.Pell.LensPairs

open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)
open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)
open E213.Math.Cohomology.Dyadic.ProductFSM
open E213.Math.Cohomology.Dyadic.ProductFSMPeriod (lens_composition_period)
open E213.Math.Cohomology.Dyadic.ProductFSMPeriodDvd (lens_composition_period_dvd)
open E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM (toBitFSM_bits_eq)


/-- ★★★★★ Lifted bit periodicity for Pell mod 3 (BitFSM form). -/
theorem pellMod3_BitFSM_bits_period_4 :
    ∀ k, (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits (k + 4)
        = (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits k :=
  fun k => (toBitFSM_bits_eq _ _ (k + 4)).trans
    ((pellFSMmod3_bits_period_4 k).trans (toBitFSM_bits_eq _ _ k).symm)

/-- ★★★★★ Lifted bit periodicity for Pell mod 5. -/
theorem pellMod5_BitFSM_bits_period_10 :
    ∀ k, (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits (k + 10)
        = (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits k :=
  fun k => (toBitFSM_bits_eq _ _ (k + 10)).trans
    ((pellFSMmod5_bits_period_10 k).trans (toBitFSM_bits_eq _ _ k).symm)

/-- ★★★★★ Lifted bit periodicity for Pell mod 7. -/
theorem pellMod7_BitFSM_bits_period_8 :
    ∀ k, (pellFSMmod7.toBitFSM (by decide : (0:Nat) < 7)).bits (k + 8)
        = (pellFSMmod7.toBitFSM (by decide : (0:Nat) < 7)).bits k :=
  fun k => (toBitFSM_bits_eq _ _ (k + 8)).trans
    ((pellFSMmod7_bits_period_8 k).trans (toBitFSM_bits_eq _ _ k).symm)

/-- ★★★★★★ Pell mod 3 × mod 7 (XOR): period | 8.  Tactic-free ∅-axiom. -/
theorem pellLens_3x7_period_8 :
    ∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 8)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 9) (m := 49) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 4 8 8 (by decide) (by decide) ⟨2, rfl⟩ ⟨1, rfl⟩
    pellMod3_BitFSM_bits_period_4 pellMod7_BitFSM_bits_period_8 k

/-- ★★★★★★ Pell mod 5 × mod 7 (XOR): period | 40.  Tactic-free ∅-axiom. -/
theorem pellLens_5x7_period_40 :
    ∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 40)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 25) (m := 49) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 10 8 40 (by decide) (by decide) ⟨4, rfl⟩ ⟨5, rfl⟩
    pellMod5_BitFSM_bits_period_10 pellMod7_BitFSM_bits_period_8 k

end E213.Math.Cohomology.Dyadic.Pell.LensPairs
