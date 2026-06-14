import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest

/-!
# SignedCut — signed Cut layer (213-native, ∅-axiom)

213-native paradigm: a *signed* `Cut` is a pair `(positive,
negative) : Cut × Cut`.  The pair **is** the signed object — the
difference-Lens applied to a directed cut-pair (`06_lens_readings.md`
§6.7; `theory/essays/analysis/integers_as_difference_lens.md`):
magnitude read Nat-style, sign Bool-style via the pair-swap
`−(a,b) = (b,a)`.  `positive − negative` is one *flattening* readout
of the pair, not the recovery of a value that lives at some exterior
layer — there is none (`05_no_exterior.md` §5.1; the tuple is the
number, `theory/math/numbersystems/slot_arithmetic.md`).  This is the
**Cayley-Dickson level-0 sign extension**, exactly mirroring
the `ComplexCut := (re, im)` pair from `Lib/Math/NumberSystems/Complex`.

Operations follow the additive group structure on pairs:
  `(a, b) + (c, d) = (a+c, b+d)`
  `−(a, b) = (b, a)`
  `(a, b) − (c, d) = (a+d, b+c)`
  `(a, b) · (c, d) = (a·c + b·d, a·d + b·c)`

No subtraction primitive on `Cut` is needed; sign tracking is
purely *structural* via the pair — `positive − negative` reads it
out, it does not name a value the pair stands in for.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Core.Core

open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- A signed `Cut`: pair (positive part, negative part). -/
abbrev SignedCut := (Nat → Nat → Bool) × (Nat → Nat → Bool)

/-- Zero signed cut: `(0, 0)`. -/
def zero : SignedCut := (constCut 0 1, constCut 0 1)

/-- One signed cut: `(1, 0)`. -/
def one : SignedCut := (constCut 1 1, constCut 0 1)

/-- Negative one signed cut: `(0, 1)`. -/
def negOne : SignedCut := (constCut 0 1, constCut 1 1)

/-- Positive embedding: `Cut → SignedCut` as `(c, 0)`. -/
def ofPos (c : Nat → Nat → Bool) : SignedCut := (c, constCut 0 1)

/-- Negative embedding: `Cut → SignedCut` as `(0, c)`. -/
def ofNeg (c : Nat → Nat → Bool) : SignedCut := (constCut 0 1, c)

/-- Positive part. -/
def pos (s : SignedCut) : Nat → Nat → Bool := s.1

/-- Negative part. -/
def neg (s : SignedCut) : Nat → Nat → Bool := s.2

/-- Negation: `−(a, b) = (b, a)`. -/
def signedNeg (s : SignedCut) : SignedCut := (s.2, s.1)

/-- Addition: `(a, b) + (c, d) = (a + c, b + d)`. -/
def signedAdd (s t : SignedCut) : SignedCut :=
  (cutSum s.1 t.1, cutSum s.2 t.2)

/-- Subtraction: `(a, b) − (c, d) = (a + d, b + c)`. -/
def signedSub (s t : SignedCut) : SignedCut :=
  (cutSum s.1 t.2, cutSum s.2 t.1)

/-- Multiplication: `(a, b) · (c, d) = (a·c + b·d, a·d + b·c)`. -/
def signedMul (s t : SignedCut) : SignedCut :=
  (cutSum (cutMul s.1 t.1) (cutMul s.2 t.2),
   cutSum (cutMul s.1 t.2) (cutMul s.2 t.1))

end E213.Lib.Math.NumberSystems.SignedCut.Core.Core
