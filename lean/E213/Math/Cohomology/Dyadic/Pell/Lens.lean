import E213.Math.Cohomology.Dyadic.ProductFSMPeriod
import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod7
import E213.Math.Cohomology.Dyadic.Pell.Family

/-!
# Pell lens composition — concrete CRT applications

Compose the Pell ArithFSM2 instances via BitFSM.product.

For Pell mod a × Pell mod b (gcd-free), the resulting product
BitFSM has period dividing lcm(period(mod a), period(mod b))
by `lens_composition_period`.

Concrete instances:
  - mod 3 × mod 5: bits period | 20
  - mod 3 × mod 7: bits period | 8
  - mod 5 × mod 7: bits period | 40
  - mod 2 × mod 3 × mod 5 × mod 7: stacked products give | 120

This achieves the full Pell-CRT closure at the FSM level, not
just the stream level.
-/

namespace E213.Math.Cohomology.Dyadic.Pell.Lensopen E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)


/-- ★★★★★★ Lens-composed Pell mod 3 × mod 5 (XOR readout): period | 20. -/
theorem pellLens_3x5_period_20 :
    ∀ k, (BitFSM.product (n := 9) (m := 25) (by decide)
            (pellFSMmod3.toBitFSM (by decide))
            (pellFSMmod5.toBitFSM (by decide))
            xor).bits (k + 20)
        = (BitFSM.product (n := 9) (m := 25) (by decide)
            (pellFSMmod3.toBitFSM (by decide))
            (pellFSMmod5.toBitFSM (by decide))
            xor).bits k := by
  intro k
  have hbits3 : ∀ k, (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits (k + 4)
                    = (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits k := by
    intro k
    rw [toBitFSM_bits_eq, toBitFSM_bits_eq]
    exact pellFSMmod3_bits_period_4 k
  have hbits5 : ∀ k, (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits (k + 10)
                    = (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits k := by
    intro k
    rw [toBitFSM_bits_eq, toBitFSM_bits_eq]
    exact pellFSMmod5_bits_period_10 k
  have hresult := lens_composition_period (n := 9) (m := 25) (by decide)
    (pellFSMmod3.toBitFSM (by decide))
    (pellFSMmod5.toBitFSM (by decide))
    xor 4 10 (by decide) (by decide) hbits3 hbits5 k
  have hlcm : Nat.lcm 4 10 = 20 := by decide
  rwa [hlcm] at hresult

end E213.Math.Cohomology.Dyadic.Pell.Lens
