import E213.Lib.Math.SignedCut.Bridge
import E213.Lib.Math.SignedCut.Inv
import E213.Lib.Math.SignedCut.UnifiedGenericInv

/-!
# SignedCut Bridge — Capstone (∅-axiom)

3 cluster witnesses + total bundle for the bridge marathon.

Closes the residual from PR #60:
  * Bridge between existing `Real213.Signed.SignedCut`
    (magnitude-sign) and `Math.SignedCut.Core.SignedCut`
    (Cayley-Dickson pair).
  * `signedInv` for cutInv-side bridge to generic x.
  * Unified generic-x cutInv via `signedGeomLimitOf`.
-/

namespace E213.Lib.Math.SignedCut.BridgeCapstone

open E213.Lib.Math.SignedCut.Core (SignedCut ofPos ofNeg signedNeg)
open E213.Lib.Math.SignedCut.Bridge
  (fromMagSign fromMagSign_pos fromMagSign_neg
   fromMagSign_neg_distrib)
open E213.Lib.Math.SignedCut.Inv
  (signedInvPos signedInvPos_pos_part signedInvPos_neg_part
   signedNeg_signedInvPos)
open E213.Lib.Math.SignedCut.UnifiedGenericInv
  (signedGeomLimitOf signedGeomLimitOf_pos signedGeomLimitOf_neg
   unified_fixpoint)
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Real213.CutInv (cutInv)

/-- ★ **Bridge witness** (magnitude-sign ↔ pair). -/
theorem bridge_witness (c : Nat → Nat → Bool) :
    fromMagSign { sign := true, cut := c } = ofPos c
    ∧ fromMagSign { sign := false, cut := c } = ofNeg c :=
  ⟨fromMagSign_pos c, fromMagSign_neg c⟩

/-- ★ **Inverse witness**. -/
theorem inv_witness (c : Nat → Nat → Bool) :
    E213.Lib.Math.SignedCut.Core.pos (signedInvPos c) = cutInv c
    ∧ E213.Lib.Math.SignedCut.Core.neg (signedInvPos c) = constCut 0 1
    ∧ signedNeg (signedInvPos c) = E213.Lib.Math.SignedCut.Inv.signedInvNeg c :=
  ⟨signedInvPos_pos_part c, signedInvPos_neg_part c,
   signedNeg_signedInvPos c⟩

/-- ★ **Unified generic-x witness**. -/
theorem unified_witness (x : Nat → Nat → Bool) (N : Nat) :
    E213.Lib.Math.SignedCut.Core.pos (signedGeomLimitOf x)
        = cutInv (E213.Lib.Math.SignedCut.Core.pos
                    (E213.Lib.Math.SignedCut.GenericGeomBridge.oneMinus x))
    ∧ E213.Lib.Math.SignedCut.Core.neg (signedGeomLimitOf x)
        = constCut 0 1
    ∧ E213.Lib.Math.Real213.CutLogODE.geomPartialSum x 0 = constCut 0 1 :=
  ⟨signedGeomLimitOf_pos x, signedGeomLimitOf_neg x,
   (unified_fixpoint x N).1⟩

/-- ★★★ **Total witness** ★★★. -/
theorem total_witness (c : Nat → Nat → Bool) (x : Nat → Nat → Bool) :
    fromMagSign { sign := true, cut := c } = ofPos c
    ∧ E213.Lib.Math.SignedCut.Core.pos (signedInvPos c) = cutInv c
    ∧ E213.Lib.Math.SignedCut.Core.pos (signedGeomLimitOf x)
        = cutInv (E213.Lib.Math.SignedCut.Core.pos
                    (E213.Lib.Math.SignedCut.GenericGeomBridge.oneMinus x)) :=
  ⟨fromMagSign_pos c, signedInvPos_pos_part c, signedGeomLimitOf_pos x⟩

end E213.Lib.Math.SignedCut.BridgeCapstone
