import E213.Math.Real213.SignedSum

import E213.Math.Real213.Core
import E213.Math.Real213.Signed
/-!
# CutDistance: cut-level distance function

|x - y| via abs ∘ signed-sub.

## Definition

cutAbs s := { sign := true, cut := s.cut } — absolute value.
cutDistance sx sy := cutAbs (cutSignedSub sx sy).
-/

namespace E213.Math.Real213.CutDistance

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.Signed (SignedCut)
open E213.Math.Real213.SignedSum (cutSignedSub cutSignedSum)
open E213.Math.Real213.Signed (signedConstCut cutNeg cutSignedMul)

/-- **cutAbs**: absolute value (flip sign to positive). -/
def cutAbs (s : SignedCut) : SignedCut := { sign := true, cut := s.cut }

/-- **cutDistance**: |x - y| via abs ∘ signed-sub. -/
def cutDistance (sx sy : SignedCut) : SignedCut :=
  cutAbs (cutSignedSub sx sy)

/-- abs idempotent. -/
theorem cutAbs_idempotent (s : SignedCut) : cutAbs (cutAbs s) = cutAbs s := rfl

/-- abs sign is always positive. -/
theorem cutAbs_sign (s : SignedCut) : (cutAbs s).sign = true := rfl

/-- abs cut = original cut (sign-independent). -/
theorem cutAbs_cut (s : SignedCut) : (cutAbs s).cut = s.cut := rfl

/-- |−x| = |x|: abs forgets sign. -/
theorem cutAbs_cutNeg (s : SignedCut) : cutAbs (cutNeg s) = cutAbs s := rfl

/-- −|x| has sign := false, cut unchanged. -/
theorem cutNeg_cutAbs (s : SignedCut) :
    cutNeg (cutAbs s) = { sign := false, cut := s.cut } := rfl

/-- abs of a signed const = positive const. -/
theorem cutAbs_signedConstCut (sign : Bool) (a b : Nat) :
    cutAbs (signedConstCut sign a b) = signedConstCut true a b := rfl

/-- |x*y| = |x|*|y|: abs distributes over signed mul. -/
theorem cutAbs_cutSignedMul (sx sy : SignedCut) :
    cutAbs (cutSignedMul sx sy)
    = cutSignedMul (cutAbs sx) (cutAbs sy) := rfl

end E213.Math.Real213.CutDistance
