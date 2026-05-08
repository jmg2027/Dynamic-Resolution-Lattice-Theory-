import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Real213.CutSum
import E213.Lib.Math.Real213.CutSumTest

/-!
# SignedCut — signed Cut layer (213-native, ∅-axiom)

213-native paradigm: a *signed* `Cut` is a pair `(positive,
negative) : Cut × Cut` where the represented value is
`positive − negative` at the underlying real.  This is the
**Cayley-Dickson level-0 sign extension**, exactly mirroring
the `ComplexCut := (re, im)` pair from `Lib/Math/Complex`.

Operations follow the additive group structure on pairs:
  `(a, b) + (c, d) = (a+c, b+d)`
  `−(a, b) = (b, a)`
  `(a, b) − (c, d) = (a+d, b+c)`
  `(a, b) · (c, d) = (a·c + b·d, a·d + b·c)`

No subtraction primitive on `Cut` is needed; sign tracking is
purely *structural* via the pair.  The "value" is recovered by
`positive − negative` at the implicit real layer (oracle).
-/

namespace E213.Lib.Math.SignedCut.Core

open E213.Lib.Math.Real213.CutSum (cutSum)
open E213.Lib.Math.Real213.CutMul (cutMul)
open E213.Lib.Math.Real213.CutSumTest (constCut)

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

end E213.Lib.Math.SignedCut.Core
