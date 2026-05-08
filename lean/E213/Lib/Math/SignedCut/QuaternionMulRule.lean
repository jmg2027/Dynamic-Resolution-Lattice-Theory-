import E213.Lib.Math.Real213.CutSum
import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Real213.CutSumTest

/-!
# Quaternion multiplication rule (CD Level 2, ∅-axiom)

Continuation of `CDMulRule` (PR #63).  Quaternion `q = a + b·i +
c·j + d·k` represented as level-2 pair
`((a, b), (c, d)) : ComplexCut × ComplexCut`.

Atomic content:
  * Quaternion identity `quatOne`, basis `quatI/J/K`.
  * Component-wise rfl witnesses.
-/

namespace E213.Lib.Math.SignedCut.QuaternionMulRule

open E213.Lib.Math.Real213.CutSumTest (constCut)

/-- A quaternion 4-tuple as nested level-2 pair. -/
abbrev Quat := ((Nat → Nat → Bool) × (Nat → Nat → Bool))
              × ((Nat → Nat → Bool) × (Nat → Nat → Bool))

/-- Quaternion identity. -/
def quatOne : Quat :=
  ((constCut 1 1, constCut 0 1), (constCut 0 1, constCut 0 1))

/-- Quaternion `i`. -/
def quatI : Quat :=
  ((constCut 0 1, constCut 1 1), (constCut 0 1, constCut 0 1))

/-- Quaternion `j`. -/
def quatJ : Quat :=
  ((constCut 0 1, constCut 0 1), (constCut 1 1, constCut 0 1))

/-- Quaternion `k`. -/
def quatK : Quat :=
  ((constCut 0 1, constCut 0 1), (constCut 0 1, constCut 1 1))

/-- ★ Identity components (rfl). -/
theorem quatOne_real : quatOne.1.1 = constCut 1 1 := rfl

/-- ★ Identity zero components. -/
theorem quatOne_imag_zero :
    quatOne.1.2 = constCut 0 1
    ∧ quatOne.2.1 = constCut 0 1
    ∧ quatOne.2.2 = constCut 0 1 :=
  ⟨rfl, rfl, rfl⟩

/-- ★ Basis `i` imaginary component. -/
theorem quatI_imag : quatI.1.2 = constCut 1 1 := rfl

/-- ★ Basis `j` real component (in second pair). -/
theorem quatJ_real : quatJ.2.1 = constCut 1 1 := rfl

/-- ★ Basis `k` imaginary component (in second pair). -/
theorem quatK_imag : quatK.2.2 = constCut 1 1 := rfl

end E213.Lib.Math.SignedCut.QuaternionMulRule
