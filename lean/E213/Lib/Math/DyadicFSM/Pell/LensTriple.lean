import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Pell.LensPairs

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.BitFSM
import E213.Lib.Math.DyadicFSM.Pell.Lens
import E213.Lib.Math.DyadicFSM.ProductFSM
import E213.Lib.Math.DyadicFSM.ProductFSMPeriod
import E213.Lib.Math.DyadicFSM.ProductFSMPeriodDvd
/-!
# Pell lens — triple product mod 3 × 5 × 7

Demonstrates lens composition stacking: ((mod3 × mod5) × mod7),
encoded into BitFSM(9·25·49) = BitFSM(11025).
Inherits period | lcm(4, 10, 8) = 40.
-/

namespace E213.Lib.Math.DyadicFSM.Pell.LensTriple

open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5)
open E213.Lib.Math.DyadicFSM.BitFSM (BitFSM)
open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.ProductFSM
open E213.Lib.Math.DyadicFSM.ProductFSMPeriod (lens_composition_period)
open E213.Lib.Math.DyadicFSM.ProductFSMPeriodDvd (lens_composition_period_dvd)
open E213.Lib.Math.DyadicFSM.Pell.Lens (pellLens_3x5_period_20)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7)
open E213.Lib.Math.DyadicFSM.Pell.LensPairs (pellMod7_BitFSM_bits_period_8)


/-- Inner product (mod 3 × mod 5). -/
def pellInner35 : BitFSM (9 * 25) :=
  E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product (by decide : (0:Nat) < 25)
    (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
    (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
    xor

/-- Inner product has period | 20. -/
theorem pellInner35_period_20 :
    ∀ k, pellInner35.bits (k + 20) = pellInner35.bits k :=
  pellLens_3x5_period_20

/-- ★★★★★★★ Pell mod 3 × 5 × 7 (stacked XOR): period | 40.
    Tactic-free ∅-axiom. -/
theorem pellLens_3x5x7_period_40 :
    ∀ k, (E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 40)
        = (E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := fun k =>
  lens_composition_period_dvd
    (n := 9 * 25) (m := 49) (by decide)
    pellInner35
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 20 8 40 (by decide) (by decide) ⟨2, rfl⟩ ⟨5, rfl⟩
    pellInner35_period_20 pellMod7_BitFSM_bits_period_8 k

end E213.Lib.Math.DyadicFSM.Pell.LensTriple
