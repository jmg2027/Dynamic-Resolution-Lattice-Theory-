import E213.Research.Real213SignedSum

/-!
# Research.Real213CutDistance: cut-level distance function

|x - y| via abs ∘ signed-sub.

## 정의

cutAbs s := { sign := true, cut := s.cut } — 절댓값.
cutDistance sx sy := cutAbs (cutSignedSub sx sy).
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **cutAbs**: absolute value (flip sign to positive). -/
def cutAbs (s : SignedCut) : SignedCut := { sign := true, cut := s.cut }

/-- **cutDistance**: |x - y| via abs ∘ signed-sub. -/
def cutDistance (sx sy : SignedCut) : SignedCut :=
  cutAbs (cutSignedSub sx sy)

/-- abs idempotent. -/
theorem cutAbs_idempotent (s : SignedCut) : cutAbs (cutAbs s) = cutAbs s := rfl

/-- abs sign 항상 positive. -/
theorem cutAbs_sign (s : SignedCut) : (cutAbs s).sign = true := rfl

end E213.Research.Real213CutSum
