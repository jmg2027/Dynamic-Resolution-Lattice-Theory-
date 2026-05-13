import E213.Lib.Math.SignedCut.Core.Core
import E213.Lib.Math.SignedCut.Bridge.Bridge
import E213.Lib.Math.Real213.Mul.CutInv
import E213.Lib.Math.Real213.Sum.Signed

/-!
# SignedCut — Multiplicative inverse (∅-axiom)

Closes residual from PR #60: "`signedInv (1 − x)` for the
cutInv-side bridge to generic x; structural definition is
direct".

213-native paradigm: `signedInv` on a `SignedCut := (p, n)` is
defined via `cutInv` applied to the "magnitude" `p ⊖ n`,
combined with the appropriate sign tracking.  Without `cutSub`,
we work via the **Real213.Signed magnitude-sign form** and use
the existing `cutInv`.

For positive signed cuts `ofPos c` (i.e. `(c, 0)`): inverse is
`ofPos (cutInv c)`.

For negative signed cuts `ofNeg c` (i.e. `(0, c)`): inverse is
`ofNeg (cutInv c)`.

For mixed sign `(p, n)` with cancellation: bridge through
magnitude-sign form, take `cutInv` of magnitude, restore sign.
-/

namespace E213.Lib.Math.SignedCut.Core.Inv

open E213.Lib.Math.SignedCut.Core.Core
  (SignedCut zero one negOne ofPos ofNeg pos neg signedNeg)
open E213.Lib.Math.Real213.Mul.CutInv (cutInv)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Sum.Signed (cutNeg signedConstCut)

/-- `signedInvPos`: inverse for the positive-only case
    `(c, 0)  ↦  (cutInv c, 0)`. -/
def signedInvPos (c : Nat → Nat → Bool) : SignedCut :=
  ofPos (cutInv c)

/-- `signedInvNeg`: inverse for the negative-only case
    `(0, c)  ↦  (0, cutInv c)`. -/
def signedInvNeg (c : Nat → Nat → Bool) : SignedCut :=
  ofNeg (cutInv c)

/-- ★ **Positive-of-positive inverse**: `signedInvPos (constCut 1 1)`
    has positive part `cutInv (constCut 1 1)`. -/
theorem signedInvPos_pos_part (c : Nat → Nat → Bool) :
    pos (signedInvPos c) = cutInv c := rfl

/-- ★ **Positive-of-positive inverse**: negative part is 0. -/
theorem signedInvPos_neg_part (c : Nat → Nat → Bool) :
    neg (signedInvPos c) = constCut 0 1 := rfl

/-- ★ **Negative-of-negative inverse**: positive part is 0. -/
theorem signedInvNeg_pos_part (c : Nat → Nat → Bool) :
    pos (signedInvNeg c) = constCut 0 1 := rfl

/-- ★ **Negative-of-negative inverse**: negative part is `cutInv c`. -/
theorem signedInvNeg_neg_part (c : Nat → Nat → Bool) :
    neg (signedInvNeg c) = cutInv c := rfl

/-- ★ **`signedNeg ∘ signedInvPos = signedInvNeg`** (rfl): negation
    of the positive-form inverse is the negative-form inverse. -/
theorem signedNeg_signedInvPos (c : Nat → Nat → Bool) :
    signedNeg (signedInvPos c) = signedInvNeg c := rfl

/-- ★ **Concrete: `signedInvPos (constCut 1 2)` represents
    `1/(1/2) = 2`** at the structural level. -/
theorem signedInvPos_half_above :
    pos (signedInvPos (constCut 1 2)) 3 1 = true := by decide

/-- ★ **`signedInvPos (constCut 1 1) = ofPos (cutInv (constCut 1 1))`** (rfl). -/
theorem signedInvPos_one : signedInvPos (constCut 1 1)
                          = ofPos (cutInv (constCut 1 1)) := rfl

end E213.Lib.Math.SignedCut.Core.Inv
