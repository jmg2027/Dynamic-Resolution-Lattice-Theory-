import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutMulComm

/-!
# Research.Real213Signed: signed Real213 + negation (F3)

F3 of `F0_213_native_arithmetic_synthesis.md`.  The native form of Real213
is *non-negative* ratios (both (a, b) of abLens.view are ≥ 0).
Sign extension for representing negatives.

## Definition

```
structure SignedCut where
  sign : Bool  -- true = positive, false = negative
  cut : Nat → Nat → Bool  -- absolute value cut
```

Negation = sign flip.

## Significance

- Real213's native is non-negative — negatives are a *separate layer*.
- The 213 axiom itself has two *symmetric* distinct atoms a, b — sign
  is attached externally, as a layer above the framework axiom.
- Bishop also defines signed reals as |abs| × sign.
-/

namespace E213.Math.Real213.Signed

open E213.Firmware E213.Hypervisor
open E213.Research.ArchimedeanCauchy

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

/-- cutSignedMul commutativity. -/
theorem cutSignedMul_comm (sx sy : SignedCut) :
    cutSignedMul sx sy = cutSignedMul sy sx := by
  show ({ sign := sx.sign == sy.sign, cut := cutMul sx.cut sy.cut } : SignedCut)
     = { sign := sy.sign == sx.sign, cut := cutMul sy.cut sx.cut }
  congr 1
  · cases sx.sign <;> cases sy.sign <;> rfl
  · funext m k; exact cutMul_comm _ _ m k

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

end E213.Math.Real213.Signed
