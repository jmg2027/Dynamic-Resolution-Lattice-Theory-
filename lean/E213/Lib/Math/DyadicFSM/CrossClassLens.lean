import E213.Lib.Math.DyadicFSM.Pell.LensPairs
import E213.Lib.Math.DyadicFSM.ArithFSM.V3Bound
import E213.Lib.Math.DyadicFSM.ProductFSMPeriodDvd

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.Mod5
import E213.Lib.Math.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM
import E213.Lib.Math.DyadicFSM.BitFSM
import E213.Lib.Math.DyadicFSM.ProductFSM
/-!
# Cross-class lens — Pell (quadratic) × Tribonacci (cubic)

Demonstrates universality of `lens_composition_period`: it operates
at BitFSM level, so it doesn't care whether components originated
from ArithFSM2 (quadratic) or ArithFSM3 (cubic).

Pell mod 3 × Tribonacci mod 2:
  - Pell mod 3:  BitFSM(9), bit period 4
  - Trib mod 2:  BitFSM(8), bit period 4
  - Product:     BitFSM(72), period | lcm(4, 4) = 4
-/

namespace E213.Lib.Math.DyadicFSM.CrossClassLens

open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5)
open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (tribFSMmod2 tribFSMmod2_bits_period_4)
open E213.Lib.Math.DyadicFSM.ArithFSM.V3Bound (toBitFSM3_bits_eq)
open E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM
open E213.Lib.Math.DyadicFSM.Pell.LensPairs
  (pellMod3_BitFSM_bits_period_4 pellMod5_BitFSM_bits_period_10)
open E213.Lib.Math.DyadicFSM.BitFSM (BitFSM)
open E213.Lib.Math.DyadicFSM.ProductFSM
open E213.Lib.Math.DyadicFSM.ProductFSMPeriodDvd (lens_composition_period_dvd)


/-- Lifted bit periodicity for Tribonacci mod 2 (BitFSM form). -/
theorem tribMod2_BitFSM_bits_period_4 :
    ∀ k, (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
            (by decide : (0:Nat) < 2) tribFSMmod2).bits (k + 4)
        = (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
            (by decide : (0:Nat) < 2) tribFSMmod2).bits k := by
  intro k
  rw [toBitFSM3_bits_eq, toBitFSM3_bits_eq]
  exact tribFSMmod2_bits_period_4 k

/-- ★★★★★★ Cross-class: Pell mod 3 × Tribonacci mod 2: period | 4.
    ∅-axiom via `lens_composition_period_dvd` (explicit `L = 4` with
    dvd witnesses `⟨1, rfl⟩` for both `4 ∣ 4`). -/
theorem crossLens_pell3_trib2_period_4 :
    ∀ k, (BitFSM.product (n := 9) (m := 8) (by decide)
            (pellFSMmod3.toBitFSM (by decide))
            (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
              (by decide) tribFSMmod2)
            xor).bits (k + 4)
        = (BitFSM.product (n := 9) (m := 8) (by decide)
            (pellFSMmod3.toBitFSM (by decide))
            (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
              (by decide) tribFSMmod2)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 9) (m := 8) (by decide)
    (pellFSMmod3.toBitFSM (by decide))
    (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
              (by decide) tribFSMmod2)
    xor 4 4 4 (by decide) (by decide) ⟨1, rfl⟩ ⟨1, rfl⟩
    pellMod3_BitFSM_bits_period_4 tribMod2_BitFSM_bits_period_4 k

/-- ★★★★★★ Cross-class: Pell mod 5 × Tribonacci mod 2: period | 20.
    ∅-axiom via `lens_composition_period_dvd` (explicit `L = 20` with
    dvd witnesses `⟨2, rfl⟩` for `10 ∣ 20` and `⟨5, rfl⟩` for `4 ∣ 20`). -/
theorem crossLens_pell5_trib2_period_20 :
    ∀ k, (BitFSM.product (n := 25) (m := 8) (by decide)
            (pellFSMmod5.toBitFSM (by decide))
            (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
              (by decide) tribFSMmod2)
            xor).bits (k + 20)
        = (BitFSM.product (n := 25) (m := 8) (by decide)
            (pellFSMmod5.toBitFSM (by decide))
            (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
              (by decide) tribFSMmod2)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 25) (m := 8) (by decide)
    (pellFSMmod5.toBitFSM (by decide))
    (E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM.ArithFSM3.toBitFSM
              (by decide) tribFSMmod2)
    xor 10 4 20 (by decide) (by decide) ⟨2, rfl⟩ ⟨5, rfl⟩
    pellMod5_BitFSM_bits_period_10 tribMod2_BitFSM_bits_period_4 k

end E213.Lib.Math.DyadicFSM.CrossClassLens
