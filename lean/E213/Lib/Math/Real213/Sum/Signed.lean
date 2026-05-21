import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Real213.Mul.CutMulComm

/-!
# Signed: signed Real213 + negation

The native form of Real213 is *non-negative* ratios (both (a, b)
of abLens.view are ≥ 0).  This module is the sign-extension
layer for representing negatives.

## Definition

```
structure SignedCut where
  sign : Bool  -- true = positive, false = negative
  cut : Nat → Nat → Bool  -- absolute value cut
```

Negation = sign flip.

## Significance

- Real213's native cut is non-negative.  SignedCut adds a Boolean
  sign reading (the second Boolean atom), giving the same residue
  space a two-Boolean-dimension reading.
- The 213 axiom's two symmetric distinct atoms `a, b` already
  carry a parity structure; SignedCut reads the parity as sign.
- Bishop also defines signed reals as |abs| × sign — same
  decomposition, different Lens vocabulary.
-/

namespace E213.Lib.Math.Real213.Sum.Signed

open E213.Theory E213.Lens
open E213.Lib.Math.Cauchy.Archimedean
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Mul.CutMulComm (cutMul_comm)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- Signed cut: sign + absolute-value cut. -/
structure SignedCut where
  sign : Bool
  cut : Nat → Nat → Bool

/-- **cutNeg**: sign flip. -/
def cutNeg (s : SignedCut) : SignedCut :=
  { sign := !s.sign, cut := s.cut }

/-- Involutivity of negation. -/
theorem cutNeg_cutNeg (s : SignedCut) : cutNeg (cutNeg s) = s := by
  cases s with
  | mk sign cut =>
    cases sign <;> rfl

/-- Sign-aware constant cut. -/
def signedConstCut (sign : Bool) (a b : Nat) : SignedCut :=
  { sign := sign, cut := constCut a b }

/-- Negation of positive 1 = negative 1. -/
example : cutNeg (signedConstCut true 1 1)
        = signedConstCut false 1 1 := rfl

/-- Negation of negative 1 = positive 1. -/
example : cutNeg (signedConstCut false 1 1)
        = signedConstCut true 1 1 := rfl

/-- **cutSignedMul**: signed multiplication via |abs| cutMul + sign rule. -/
def cutSignedMul (sx sy : SignedCut) : SignedCut where
  sign := sx.sign == sy.sign
  cut := cutMul sx.cut sy.cut

/-- (+1) * (+1) = (+1).  At cut (1, 1): true. -/
example : (cutSignedMul (signedConstCut true 1 1)
                       (signedConstCut true 1 1)).cut 1 1 = true := by decide

/-- (-1) * (-1) = (+1).  Sign true. -/
example : (cutSignedMul (signedConstCut false 1 1)
                       (signedConstCut false 1 1)).sign = true := by decide

/-- (+1) * (-1) = (-1).  Sign false. -/
example : (cutSignedMul (signedConstCut true 1 1)
                       (signedConstCut false 1 1)).sign = false := by decide

/-- cutNeg of signedConstCut: flips sign. -/
theorem cutNeg_signedConstCut (sign : Bool) (a b : Nat) :
    cutNeg (signedConstCut sign a b) = signedConstCut (!sign) a b := rfl

/-- cutSignedMul commutativity (signed-cutEq form, PURE):
    same sign equality + pointwise cut equality. -/
theorem cutSignedMul_comm (sx sy : SignedCut) :
    (cutSignedMul sx sy).sign = (cutSignedMul sy sx).sign
    ∧ ∀ m k, (cutSignedMul sx sy).cut m k = (cutSignedMul sy sx).cut m k := by
  refine ⟨?_, ?_⟩
  · show (sx.sign == sy.sign) = (sy.sign == sx.sign)
    cases sx.sign <;> cases sy.sign <;> rfl
  · intro m k
    show cutMul sx.cut sy.cut m k = cutMul sy.cut sx.cut m k
    exact cutMul_comm _ _ m k

/-- cutNeg distributes over cutSignedMul on the left. -/
theorem cutNeg_cutSignedMul_left (sx sy : SignedCut) :
    cutNeg (cutSignedMul sx sy) = cutSignedMul (cutNeg sx) sy := by
  show ({ sign := !(sx.sign == sy.sign), cut := cutMul sx.cut sy.cut } : SignedCut)
     = { sign := (!sx.sign) == sy.sign, cut := cutMul sx.cut sy.cut }
  congr 1
  cases sx.sign <;> cases sy.sign <;> rfl

/-- cutNeg distributes over cutSignedMul on the right. -/
theorem cutNeg_cutSignedMul_right (sx sy : SignedCut) :
    cutNeg (cutSignedMul sx sy) = cutSignedMul sx (cutNeg sy) := by
  show ({ sign := !(sx.sign == sy.sign), cut := cutMul sx.cut sy.cut } : SignedCut)
     = { sign := sx.sign == (!sy.sign), cut := cutMul sx.cut sy.cut }
  congr 1
  cases sx.sign <;> cases sy.sign <;> rfl

end E213.Lib.Math.Real213.Sum.Signed
