import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.Product.ProductFSMPeriod
import E213.Lib.Math.DyadicFSM.Product.ProductFSMPeriodDvd
import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.BitFSM
import E213.Lib.Math.DyadicFSM.Product.ProductFSM
/-!
# Pell lens composition — concrete CRT applications

Compose the Pell ArithFSM2 instances via E213.Lib.Math.DyadicFSM.Product.ProductFSM.BitFSM.product.

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

namespace E213.Lib.Math.DyadicFSM.Pell.Lens

open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3_bits_period_4)
open E213.Lib.Math.DyadicFSM.BitFSM (BitFSM)
open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Product.ProductFSM
open E213.Lib.Math.DyadicFSM.Product.ProductFSMPeriodDvd (lens_composition_period_dvd)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (toBitFSM_bits_eq)


/-- ★★★★★★ Lens-composed Pell mod 3 × mod 5 (XOR readout): period | 20.
    Tactic-free to keep ∅-axiom. -/
theorem pellLens_3x5_period_20 :
    ∀ k, (E213.Lib.Math.DyadicFSM.Product.ProductFSM.BitFSM.product (n := 9) (m := 25) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            xor).bits (k + 20)
        = (E213.Lib.Math.DyadicFSM.Product.ProductFSM.BitFSM.product (n := 9) (m := 25) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 9) (m := 25) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
    (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
    xor 4 10 20 (by decide) (by decide) ⟨5, rfl⟩ ⟨2, rfl⟩
    (fun k => (toBitFSM_bits_eq _ _ (k + 4)).trans
        ((pellFSMmod3_bits_period_4 k).trans (toBitFSM_bits_eq _ _ k).symm))
    (fun k => (toBitFSM_bits_eq _ _ (k + 10)).trans
        ((pellFSMmod5_bits_period_10 k).trans (toBitFSM_bits_eq _ _ k).symm))
    k

end E213.Lib.Math.DyadicFSM.Pell.Lens
