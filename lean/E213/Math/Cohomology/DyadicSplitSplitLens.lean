import E213.Math.Cohomology.DyadicProductFSMPeriod
import E213.Math.Cohomology.DyadicArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicArithFSMmod11
import E213.Math.Cohomology.DyadicArithFSMmod19

/-!
# Lens composition — split × split (Pell mod 11 × mod 19)

Both component primes are SPLIT (Legendre 5 = QR), with bit
periods 5 and 9 respectively.  Their lens composition has period
| lcm(5, 9) = 45.

This is the first SPLIT × SPLIT composition, complementing the
existing INERT × INERT (3 × 7 → 8) and SPLIT × SPLIT × INERT
(3 × 5 × 7 → 40) cases.

Product BitFSM: BitFSM(11 · 19) = BitFSM(209).
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Lifted Pell mod 11 bit periodicity (BitFSM form). -/
theorem pellMod11_BitFSM_bits_period_5 :
    ∀ k, (pellFSMmod11.toBitFSM (by omega : (0:Nat) < 11)).bits (k + 5)
        = (pellFSMmod11.toBitFSM (by omega : (0:Nat) < 11)).bits k := by
  intro k
  rw [toBitFSM_bits_eq, toBitFSM_bits_eq]
  exact pellFSMmod11_bits_period_5 k

/-- Lifted Pell mod 19 bit periodicity. -/
theorem pellMod19_BitFSM_bits_period_9 :
    ∀ k, (pellFSMmod19.toBitFSM (by omega : (0:Nat) < 19)).bits (k + 9)
        = (pellFSMmod19.toBitFSM (by omega : (0:Nat) < 19)).bits k := by
  intro k
  rw [toBitFSM_bits_eq, toBitFSM_bits_eq]
  exact pellFSMmod19_bits_period_9 k

/-- ★★★★★★ Pell mod 11 × mod 19 (XOR): period | lcm(5, 9) = 45.
    First SPLIT × SPLIT composition. -/
theorem pellLens_11x19_period_45 :
    ∀ k, (BitFSM.product (n := 11 * 11) (m := 19 * 19) (by omega)
            (pellFSMmod11.toBitFSM (by omega))
            (pellFSMmod19.toBitFSM (by omega))
            xor).bits (k + 45)
        = (BitFSM.product (n := 11 * 11) (m := 19 * 19) (by omega)
            (pellFSMmod11.toBitFSM (by omega))
            (pellFSMmod19.toBitFSM (by omega))
            xor).bits k := by
  intro k
  have hresult := lens_composition_period
    (n := 11 * 11) (m := 19 * 19) (by omega)
    (pellFSMmod11.toBitFSM (by omega))
    (pellFSMmod19.toBitFSM (by omega))
    xor 5 9 (by omega) (by omega)
    pellMod11_BitFSM_bits_period_5 pellMod19_BitFSM_bits_period_9 k
  have hlcm : Nat.lcm 5 9 = 45 := by decide
  rwa [hlcm] at hresult

end E213.Math.Cohomology.DyadicConjecture
