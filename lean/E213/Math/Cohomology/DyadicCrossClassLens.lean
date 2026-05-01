import E213.Math.Cohomology.DyadicPellLensPairs
import E213.Math.Cohomology.DyadicArithFSM3Bound

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

namespace E213.Math.Cohomology.DyadicConjecture

/-- Lifted bit periodicity for Tribonacci mod 2 (BitFSM form). -/
theorem tribMod2_BitFSM_bits_period_4 :
    ∀ k, (tribFSMmod2.toBitFSM (by omega : (0:Nat) < 2)).bits (k + 4)
        = (tribFSMmod2.toBitFSM (by omega : (0:Nat) < 2)).bits k := by
  intro k
  rw [toBitFSM3_bits_eq, toBitFSM3_bits_eq]
  exact tribFSMmod2_bits_period_4 k

/-- ★★★★★★ Cross-class: Pell mod 3 × Tribonacci mod 2: period | 4. -/
theorem crossLens_pell3_trib2_period_4 :
    ∀ k, (BitFSM.product (n := 9) (m := 8) (by omega)
            (pellFSMmod3.toBitFSM (by omega))
            (tribFSMmod2.toBitFSM (by omega))
            xor).bits (k + 4)
        = (BitFSM.product (n := 9) (m := 8) (by omega)
            (pellFSMmod3.toBitFSM (by omega))
            (tribFSMmod2.toBitFSM (by omega))
            xor).bits k := by
  intro k
  have hresult := lens_composition_period (n := 9) (m := 8) (by omega)
    (pellFSMmod3.toBitFSM (by omega))
    (tribFSMmod2.toBitFSM (by omega))
    xor 4 4 (by omega) (by omega)
    pellMod3_BitFSM_bits_period_4 tribMod2_BitFSM_bits_period_4 k
  have hlcm : Nat.lcm 4 4 = 4 := by decide
  rwa [hlcm] at hresult

/-- ★★★★★★ Cross-class: Pell mod 5 × Tribonacci mod 2: period | 20. -/
theorem crossLens_pell5_trib2_period_20 :
    ∀ k, (BitFSM.product (n := 25) (m := 8) (by omega)
            (pellFSMmod5.toBitFSM (by omega))
            (tribFSMmod2.toBitFSM (by omega))
            xor).bits (k + 20)
        = (BitFSM.product (n := 25) (m := 8) (by omega)
            (pellFSMmod5.toBitFSM (by omega))
            (tribFSMmod2.toBitFSM (by omega))
            xor).bits k := by
  intro k
  have hresult := lens_composition_period (n := 25) (m := 8) (by omega)
    (pellFSMmod5.toBitFSM (by omega))
    (tribFSMmod2.toBitFSM (by omega))
    xor 10 4 (by omega) (by omega)
    pellMod5_BitFSM_bits_period_10 tribMod2_BitFSM_bits_period_4 k
  have hlcm : Nat.lcm 10 4 = 20 := by decide
  rwa [hlcm] at hresult

end E213.Math.Cohomology.DyadicConjecture
