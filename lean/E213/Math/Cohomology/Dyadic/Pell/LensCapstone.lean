import E213.Math.Cohomology.Dyadic.Pell.LensTriple

/-!
# Pell-CRT FSM-level capstone

Bundles all FSM-level lens compositions for Pell mod {3, 5, 7}:
  - 3 pairs (3×5, 3×7, 5×7) → periods | (20, 8, 40)
  - 1 triple (3×5×7)        → period  | 40

All ≤ {propext, Quot.sound}.
-/

namespace E213.Math.Cohomology.Dyadic.Pell.LensCapstone

open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5)
open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)
open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2 pellFSMmod2)
open E213.Math.Cohomology.Dyadic.ProductFSM
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod7 (pellFSMmod7)
open E213.Math.Cohomology.Dyadic.Pell.Lens (pellLens_3x5_period_20)
open E213.Math.Cohomology.Dyadic.Pell.LensPairs (pellMod7_BitFSM_bits_period_8 pellLens_3x7_period_8 pellLens_5x7_period_40)
open E213.Math.Cohomology.Dyadic.Pell.LensTriple (pellLens_3x5x7_period_40)
open E213.Math.Cohomology.Dyadic.Pell.LensTriple


/-- ★★★★★★★ Full Pell-CRT FSM-level capstone. -/
theorem pell_crt_fsm_capstone :
    (∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 25) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5) xor).bits (k + 20)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 25) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5) xor).bits k)
    ∧ (∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7) xor).bits (k + 8)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7) xor).bits k)
    ∧ (∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7) xor).bits (k + 40)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7) xor).bits k)
    ∧ (∀ k, (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7) xor).bits (k + 40)
        = (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7) xor).bits k) :=
  ⟨pellLens_3x5_period_20,
   pellLens_3x7_period_8,
   pellLens_5x7_period_40,
   pellLens_3x5x7_period_40⟩

end E213.Math.Cohomology.Dyadic.Pell.LensCapstone
