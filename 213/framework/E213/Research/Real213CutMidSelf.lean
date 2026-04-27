import E213.Research.Real213CutSumOne
import E213.Research.Real213ConstCutScale
import E213.Research.Real213CutBisection

/-!
# Research.Real213CutMidSelf: midpoint(c, c) = c for const cut

cutMid (constCut a b) (constCut a b) = constCut a b for b ≥ 1.

Via cutSum_self + cutHalf_constCut + constCut_scale.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **midpoint(c, c) = c** for c = a/b. -/
theorem cutMid_self_constCut (a b : Nat) (hb : b ≥ 1) :
    cutMid (constCut a b) (constCut a b) = constCut a b := by
  show cutHalf (cutSum (constCut a b) (constCut a b)) = constCut a b
  rw [cutSum_self, cutHalf_constCut]
  -- Goal: constCut (2*a) (2*b) = constCut a b
  have h := constCut_scale a b 2 (by decide : 2 ≥ 1)
  rw [show a*2 = 2*a from Nat.mul_comm a 2, show b*2 = 2*b from Nat.mul_comm b 2] at h
  exact h.symm

end E213.Research.Real213CutSum
