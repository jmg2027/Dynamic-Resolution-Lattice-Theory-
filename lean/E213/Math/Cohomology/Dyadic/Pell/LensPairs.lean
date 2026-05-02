import E213.Math.Cohomology.Dyadic.Pell.Lens

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
open E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM (toBitFSM_bits_eq)


/-- ★★★★★ Lifted bit periodicity for Pell mod 3 (BitFSM form). -/
theorem pellMod3_BitFSM_bits_period_4 :
    ∀ k, (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits (k + 4)
        = (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits k := by
  intro k
  rw [toBitFSM_bits_eq, toBitFSM_bits_eq]
  exact pellFSMmod3_bits_period_4 k

/-- ★★★★★ Lifted bit periodicity for Pell mod 5. -/
theorem pellMod5_BitFSM_bits_period_10 :
    ∀ k, (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits (k + 10)
        = (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits k := by
  intro k
  rw [toBitFSM_bits_eq, toBitFSM_bits_eq]
  exact pellFSMmod5_bits_period_10 k

/-- ★★★★★ Lifted bit periodicity for Pell mod 7. -/
theorem pellMod7_BitFSM_bits_period_8 :
    ∀ k, (pellFSMmod7.toBitFSM (by decide : (0:Nat) < 7)).bits (k + 8)
        = (pellFSMmod7.toBitFSM (by decide : (0:Nat) < 7)).bits k := by
  intro k
  rw [toBitFSM_bits_eq, toBitFSM_bits_eq]
  exact pellFSMmod7_bits_period_8 k

/-- ★★★★★★ Pell mod 3 × mod 7 (XOR): period | 8. -/
theorem pellLens_3x7_period_8 :
    ∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 8)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := by
  intro k
  have hresult := lens_composition_period (n := 9) (m := 49) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 4 8 (by decide) (by decide)
    pellMod3_BitFSM_bits_period_4 pellMod7_BitFSM_bits_period_8 k
  have hlcm : Nat.lcm 4 8 = 8 := by decide
  rwa [hlcm] at hresult

/-- ★★★★★★ Pell mod 5 × mod 7 (XOR): period | 40. -/
theorem pellLens_5x7_period_40 :
    ∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 40)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := by
  intro k
  have hresult := lens_composition_period (n := 25) (m := 49) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 10 8 (by decide) (by decide)
    pellMod5_BitFSM_bits_period_10 pellMod7_BitFSM_bits_period_8 k
  have hlcm : Nat.lcm 10 8 = 40 := by decide
  rwa [hlcm] at hresult

end E213.Math.Cohomology.Dyadic.Pell.LensPairs
