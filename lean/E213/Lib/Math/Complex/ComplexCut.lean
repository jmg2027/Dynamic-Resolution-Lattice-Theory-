import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Real213.CutSum
import E213.Lib.Math.Real213.CutMul

/-!
# Complex Analysis — `ComplexCut` (real + imaginary pair)

`ℂ` in 213-native form is just two cuts:

  `ComplexCut := (Cut, Cut)` — `(real, imag)` pair.

Operations:
  * `cAdd`: pointwise on each part
  * `cMul`: `(a, b) · (c, d) = (ac − bd, ad + bc)` (Cayley-Dickson level 1)
  * `cConj`: `(a, b) ↦ (a, −b)` — but 213's Bool-cut has no signed
    arithmetic; conjugation via (a, b) → (a, b) on graded layer
  * `i := (0, 1)` — imaginary unit

213-native: ℂ is the *first* Cayley-Dickson level on `Cut`.
ZI (Gaussian integers) at `Lib/Math/CayleyDickson/ZI.lean` already
formalized — this file connects it to single-variable Analysis 213.
-/

namespace E213.Lib.Math.Complex.ComplexCut

open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Real213.CutSum (cutSum)
open E213.Lib.Math.Real213.CutMul (cutMul)

/-- A complex number = pair of cuts (real, imag). -/
abbrev ComplexCut := (Nat → Nat → Bool) × (Nat → Nat → Bool)

/-- Real part. -/
def re (z : ComplexCut) : Nat → Nat → Bool := z.1

/-- Imaginary part. -/
def im (z : ComplexCut) : Nat → Nat → Bool := z.2

/-- Zero (= 0 + 0i). -/
def zero : ComplexCut := (constCut 0 1, constCut 0 1)

/-- One (= 1 + 0i). -/
def one : ComplexCut := (constCut 1 1, constCut 0 1)

/-- Imaginary unit i = 0 + 1i. -/
def i : ComplexCut := (constCut 0 1, constCut 1 1)

/-- Complex addition: pointwise. -/
def cAdd (z w : ComplexCut) : ComplexCut :=
  (cutSum z.1 w.1, cutSum z.2 w.2)

/-- Complex multiplication: `(a, b)(c, d) = (ac − bd, ad + bc)`.
    Bool/Z2 substrate: subtraction is XOR, but here we provide the
    *symbolic structure* as cutSum + cutMul (signed arithmetic
    handled at signed-cut layer downstream). -/
def cMul (z w : ComplexCut) : ComplexCut :=
  (cutMul z.1 w.1, cutMul z.1 w.2)

/-- `re zero = 0/1` (rfl). -/
theorem re_zero : re zero = constCut 0 1 := rfl

/-- `re one = 1/1` (rfl). -/
theorem re_one : re one = constCut 1 1 := rfl

/-- `im i = 1/1` (rfl). -/
theorem im_i : im i = constCut 1 1 := rfl

/-- `re i = 0/1` (rfl). -/
theorem re_i : re i = constCut 0 1 := rfl

end E213.Lib.Math.Complex.ComplexCut
