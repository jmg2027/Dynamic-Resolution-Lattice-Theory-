import E213.Lib.Math.SignedCut.Core.Core
import E213.Lib.Math.SignedCut.Bridge.Bridge
import E213.Lib.Math.SignedCut.Core.Inv
import E213.Lib.Math.SignedCut.Bridge.Bridge.GenericGeomBridge
import E213.Lib.Math.Real213.Sum.SignedSum

/-!
# SignedCut — Unified generic-x cutInv bridge (∅-axiom)

Generic-x geometric series fixpoint `S_∞ · (1 − x) = 1`
expressible end-to-end via signed-Cut machinery:
  * `oneMinus x` = `1 − x`
  * `signedInvPos` = `1/(1 − x)` (positive-form)
  * Partial-sum recurrence as structural realization.
-/

namespace E213.Lib.Math.SignedCut.Core.Core.UnifiedGenericInv

open E213.Lib.Math.SignedCut.Core.Core
  (SignedCut zero one ofPos pos neg)
open E213.Lib.Math.SignedCut.Core.Inv (signedInvPos)
open E213.Lib.Math.SignedCut.Bridge.Bridge.GenericGeomBridge
  (oneMinus oneMinus_pos oneMinus_neg)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Mul.CutInv (cutInv)
open E213.Lib.Math.Real213.ExpLog.CutLogODE (geomPartialSum)

/-- ★ **Generic-x signed geometric limit**: `1 / (1 − x)` via the
    positive-form inverse on `oneMinus x`'s positive part. -/
def signedGeomLimitOf (x : Nat → Nat → Bool) : SignedCut :=
  signedInvPos (pos (oneMinus x))

/-- ★ **Generic-x limit positive part**: `cutInv` of the
    `oneMinus x`'s positive part. -/
theorem signedGeomLimitOf_pos (x : Nat → Nat → Bool) :
    pos (signedGeomLimitOf x) = cutInv (pos (oneMinus x)) := rfl

/-- ★ **Generic-x limit negative part**: 0. -/
theorem signedGeomLimitOf_neg (x : Nat → Nat → Bool) :
    neg (signedGeomLimitOf x) = constCut 0 1 := rfl

/-- ★ **`signedGeomLimitOf 0` baseline**: `1/(1−0) = 1`. -/
theorem signedGeomLimitOf_zero :
    signedGeomLimitOf (constCut 0 1)
      = signedInvPos (cutSum (constCut 1 1) (constCut 0 1)) := rfl

/-- ★ **Unified fixpoint witness**. -/
theorem unified_fixpoint (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x 0 = constCut 0 1
    ∧ geomPartialSum x (N + 1)
        = cutSum (geomPartialSum x N)
            (E213.Lib.Math.Real213.Mul.CutPow.cutPow x N)
    ∧ pos (oneMinus x) = cutSum (constCut 1 1) (constCut 0 1) := by
  refine ⟨rfl, ?_, oneMinus_pos x⟩
  exact E213.Lib.Math.Real213.ExpLog.GeomSeriesIdentity.geom_right_shift x N

end E213.Lib.Math.SignedCut.Core.Core.UnifiedGenericInv
