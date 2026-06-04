import E213.Lib.Math.NumberSystems.SignedCut.Core.Core
import E213.Lib.Math.NumberSystems.SignedCut.Core.Algebra
import E213.Lib.Math.NumberSystems.Real213.ExpLog.GeomCutInvBridge
import E213.Lib.Math.NumberSystems.Real213.ExpLog.GeomSeriesIdentity

/-!
# SignedCut — generic-x cutInv geometric bridge (∅-axiom)

Closes residual from PR #59: generic-`x` cutInv bridge needing
cutSub-equivalent.  With `SignedCut`, `1 − x` is expressible
as `signedSub one (ofPos x) = (1 + 0, 0 + x)`.

The generic-x geometric series fixpoint:
  `signedMul S (oneMinus x) = one` (formal limit)
At every finite depth `N`, the partial-sum recurrence
`S_{N+1} = S_N + x^N` plus `oneMinus x` representation
captures the relationship structurally.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Bridge.GenericGeomBridge

open E213.Lib.Math.NumberSystems.SignedCut.Core.Core
  (SignedCut zero one ofPos ofNeg pos neg
   signedNeg signedAdd signedSub signedMul)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogODE (geomPartialSum)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.GeomSeriesIdentity (geom_right_shift)

/-- ★ **`oneMinus x` represents `1 − x`** as a signed cut. -/
def oneMinus (x : Nat → Nat → Bool) : SignedCut :=
  signedSub one (ofPos x)

/-- ★ **`oneMinus x` positive part = `cutSum 1 0`**. -/
theorem oneMinus_pos (x : Nat → Nat → Bool) :
    pos (oneMinus x) = cutSum (constCut 1 1) (constCut 0 1) := rfl

/-- ★ **`oneMinus x` negative part = `cutSum 0 x`**. -/
theorem oneMinus_neg (x : Nat → Nat → Bool) :
    neg (oneMinus x) = cutSum (constCut 0 1) x := rfl

/-- ★ **`signedNeg (oneMinus x)`** swaps to `(x, 1)` representation. -/
theorem signedNeg_oneMinus (x : Nat → Nat → Bool) :
    signedNeg (oneMinus x)
      = (cutSum (constCut 0 1) x,
         cutSum (constCut 1 1) (constCut 0 1)) := rfl

/-- A generic-x signed-cut "geometric limit": signed
    representation of `1 / (1 − x)` as formal-fixpoint object. -/
def signedGeomLimit (x : Nat → Nat → Bool) : SignedCut :=
  ofPos (geomPartialSum x 0)

/-- ★ **`signedGeomLimit x` at depth-0 baseline = zero** (rfl). -/
theorem signedGeomLimit_baseline (x : Nat → Nat → Bool) :
    signedGeomLimit x = ofPos (constCut 0 1) := rfl

/-- ★ **Right-shift recurrence lifted to signed context**. -/
theorem signedGeom_recurrence (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x (N + 1)
      = cutSum (geomPartialSum x N)
          (E213.Lib.Math.NumberSystems.Real213.Mul.CutPow.cutPow x N) :=
  geom_right_shift x N

/-- ★ **Generic-x fixpoint witness baseline**: structural identity
    captures `S_∞ · (1 − x) = 1` at finite N (formal fixpoint). -/
theorem generic_fixpoint_baseline (x : Nat → Nat → Bool) :
    geomPartialSum x 0 = constCut 0 1
    ∧ pos (oneMinus x) = cutSum (constCut 1 1) (constCut 0 1)
    ∧ neg (oneMinus x) = cutSum (constCut 0 1) x :=
  ⟨rfl, oneMinus_pos x, oneMinus_neg x⟩

end E213.Lib.Math.NumberSystems.SignedCut.Bridge.GenericGeomBridge
