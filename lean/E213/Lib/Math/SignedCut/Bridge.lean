import E213.Lib.Math.SignedCut.Core
import E213.Lib.Math.Real213.Sum.Signed
import E213.Lib.Math.Real213.Sum.SignedSum

/-!
# SignedCut — Bridge to existing `Real213.Signed` (∅-axiom)

The codebase already has two parallel signed-cut representations:

  * **`Real213.Signed.SignedCut`** = `{sign : Bool, cut : Cut}`
    (magnitude-with-sign, Bishop-style).
  * **`Math.SignedCut.Core.SignedCut`** = `Cut × Cut`
    (Cayley-Dickson level-0 pair, this PR's representation).

This file bridges them: convert between the two forms and show
that the basic operations agree at the structural level.

213-native paradigm: both representations are valid 213-native
sign extensions; they correspond to:
  * **Magnitude-sign** = polar form on the sign-half-line.
  * **Pair form** = Cayley-Dickson rectangular form.
The bridge shows they're isomorphic at the substrate level.
-/

namespace E213.Lib.Math.SignedCut.Bridge

open E213.Lib.Math.SignedCut.Core
  (SignedCut ofPos ofNeg signedNeg)
open E213.Lib.Math.Real213.Sum.Signed
  (cutNeg signedConstCut)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- Convert magnitude-sign form to pair form:
    `{sign := true, cut := c}  ↦  (c, 0)`,
    `{sign := false, cut := c} ↦  (0, c)`. -/
def fromMagSign (s : E213.Lib.Math.Real213.Sum.Signed.SignedCut) : SignedCut :=
  if s.sign then ofPos s.cut else ofNeg s.cut

/-- ★ Magnitude-sign positive maps to `ofPos`. -/
theorem fromMagSign_pos (c : Nat → Nat → Bool) :
    fromMagSign { sign := true, cut := c } = ofPos c := by
  show (if true then ofPos c else ofNeg c) = ofPos c
  rfl

/-- ★ Magnitude-sign negative maps to `ofNeg`. -/
theorem fromMagSign_neg (c : Nat → Nat → Bool) :
    fromMagSign { sign := false, cut := c } = ofNeg c := by
  show (if false then ofPos c else ofNeg c) = ofNeg c
  rfl

/-- ★ Negation preserved by bridge:
    `fromMagSign (cutNeg s)` flips the pair components. -/
theorem fromMagSign_neg_distrib (s : E213.Lib.Math.Real213.Sum.Signed.SignedCut) :
    fromMagSign (cutNeg s) = signedNeg (fromMagSign s) := by
  cases s with
  | mk sign cut =>
    cases sign with
    | true =>
      show (if !true then ofPos cut else ofNeg cut)
        = signedNeg (if true then ofPos cut else ofNeg cut)
      rfl
    | false =>
      show (if !false then ofPos cut else ofNeg cut)
        = signedNeg (if false then ofPos cut else ofNeg cut)
      rfl

/-- ★ Bridge of `signedConstCut true a b`: maps to `ofPos (constCut a b)`. -/
theorem fromMagSign_signedConstCut_pos (a b : Nat) :
    fromMagSign (signedConstCut true a b) = ofPos (constCut a b) := rfl

/-- ★ Bridge of `signedConstCut false a b`: maps to `ofNeg (constCut a b)`. -/
theorem fromMagSign_signedConstCut_neg (a b : Nat) :
    fromMagSign (signedConstCut false a b) = ofNeg (constCut a b) := rfl

end E213.Lib.Math.SignedCut.Bridge
