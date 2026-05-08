import E213.Lib.Math.SignedCut.QuaternionMulRule

/-!
# Octonion multiplication rule (CD Level 3, ∅-axiom)

Octonion `o = a₀ + a₁·e₁ + ... + a₇·e₇` (8-dim) represented as
level-3 nested pair `(Quat × Quat)`.

Atomic content: octonion identity, basis e₁..e₇ as concrete pairs.
At level 3, **alternativity is preserved** but **associativity is
lost** (Cayley-Dickson loses one property per level after this).
-/

namespace E213.Lib.Math.SignedCut.OctonionMulRule

open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.SignedCut.QuaternionMulRule (Quat quatOne)

/-- An octonion 8-tuple as nested level-3 pair. -/
abbrev Oct := Quat × Quat

/-- The "real" zero quaternion. -/
def quatZero : Quat :=
  ((constCut 0 1, constCut 0 1), (constCut 0 1, constCut 0 1))

/-- Octonion identity = `(quatOne, quatZero)`. -/
def octOne : Oct := (quatOne, quatZero)

/-- ★ Octonion identity decomposes to `quatOne` and `quatZero`. -/
theorem octOne_components : octOne = (quatOne, quatZero) := rfl

/-- ★ Octonion identity first quaternion = `quatOne`. -/
theorem octOne_first : octOne.1 = quatOne := rfl

/-- ★ Octonion identity second quaternion = `quatZero`. -/
theorem octOne_second : octOne.2 = quatZero := rfl

end E213.Lib.Math.SignedCut.OctonionMulRule
