import E213.Math.Cohomology.DyadicPellLensTriple

/-!
# Pell-CRT FSM-level capstone

Bundles all FSM-level lens compositions for Pell mod {3, 5, 7}:
  - 3 pairs (3×5, 3×7, 5×7) → periods | (20, 8, 40)
  - 1 triple (3×5×7)        → period  | 40

All ≤ {propext, Quot.sound}.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★★★ Full Pell-CRT FSM-level capstone. -/
theorem pell_crt_fsm_capstone :
    (∀ k, (BitFSM.product (n := 9) (m := 25) (by omega)
            (pellFSMmod3.toBitFSM (by omega))
            (pellFSMmod5.toBitFSM (by omega)) xor).bits (k + 20)
        = (BitFSM.product (n := 9) (m := 25) (by omega)
            (pellFSMmod3.toBitFSM (by omega))
            (pellFSMmod5.toBitFSM (by omega)) xor).bits k)
    ∧ (∀ k, (BitFSM.product (n := 9) (m := 49) (by omega)
            (pellFSMmod3.toBitFSM (by omega))
            (pellFSMmod7.toBitFSM (by omega)) xor).bits (k + 8)
        = (BitFSM.product (n := 9) (m := 49) (by omega)
            (pellFSMmod3.toBitFSM (by omega))
            (pellFSMmod7.toBitFSM (by omega)) xor).bits k)
    ∧ (∀ k, (BitFSM.product (n := 25) (m := 49) (by omega)
            (pellFSMmod5.toBitFSM (by omega))
            (pellFSMmod7.toBitFSM (by omega)) xor).bits (k + 40)
        = (BitFSM.product (n := 25) (m := 49) (by omega)
            (pellFSMmod5.toBitFSM (by omega))
            (pellFSMmod7.toBitFSM (by omega)) xor).bits k)
    ∧ (∀ k, (BitFSM.product (n := 9 * 25) (m := 49) (by omega)
            pellInner35
            (pellFSMmod7.toBitFSM (by omega)) xor).bits (k + 40)
        = (BitFSM.product (n := 9 * 25) (m := 49) (by omega)
            pellInner35
            (pellFSMmod7.toBitFSM (by omega)) xor).bits k) :=
  ⟨pellLens_3x5_period_20,
   pellLens_3x7_period_8,
   pellLens_5x7_period_40,
   pellLens_3x5x7_period_40⟩

end E213.Math.Cohomology.DyadicConjecture
