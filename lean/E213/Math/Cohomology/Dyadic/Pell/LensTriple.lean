import E213.Math.Cohomology.Dyadic.Pell.LensPairs

/-!
# Pell lens — triple product mod 3 × 5 × 7

Demonstrates lens composition stacking: ((mod3 × mod5) × mod7),
encoded into BitFSM(9·25·49) = BitFSM(11025).
Inherits period | lcm(4, 10, 8) = 40.
-/

namespace E213.Math.Cohomology.Dyadic.Pell.LensTripleopen E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5)
open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)


/-- Inner product (mod 3 × mod 5). -/
def pellInner35 : BitFSM (9 * 25) :=
  BitFSM.product (by decide : (0:Nat) < 25)
    (pellFSMmod3.toBitFSM (by decide))
    (pellFSMmod5.toBitFSM (by decide))
    xor

/-- Inner product has period | 20. -/
theorem pellInner35_period_20 :
    ∀ k, pellInner35.bits (k + 20) = pellInner35.bits k :=
  pellLens_3x5_period_20

/-- ★★★★★★★ Pell mod 3 × 5 × 7 (stacked XOR): period | 40. -/
theorem pellLens_3x5x7_period_40 :
    ∀ k, (BitFSM.product (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (pellFSMmod7.toBitFSM (by decide))
            xor).bits (k + 40)
        = (BitFSM.product (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (pellFSMmod7.toBitFSM (by decide))
            xor).bits k := by
  intro k
  have hresult := lens_composition_period
    (n := 9 * 25) (m := 49) (by decide)
    pellInner35
    (pellFSMmod7.toBitFSM (by decide))
    xor 20 8 (by decide) (by decide)
    pellInner35_period_20 pellMod7_BitFSM_bits_period_8 k
  have hlcm : Nat.lcm 20 8 = 40 := by decide
  rwa [hlcm] at hresult

end E213.Math.Cohomology.Dyadic.Pell.LensTriple
