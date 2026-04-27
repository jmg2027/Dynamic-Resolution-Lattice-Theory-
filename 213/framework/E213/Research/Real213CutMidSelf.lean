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

/-- **midpoint(a/2, c/2) = (a+c)/4** for any a, c. -/
theorem cutMid_half_general (a c : Nat) :
    cutMid (constCut a 2) (constCut c 2) = constCut (a+c) 4 := by
  show cutHalf (cutSum (constCut a 2) (constCut c 2)) = constCut (a+c) 4
  rw [cutSum_half_general, cutHalf_constCut]

/-- **midpoint(a/1, c/1) = (a+c)/2** for any integers a, c. -/
theorem cutMid_int_int (a c : Nat) :
    cutMid (constCut a 1) (constCut c 1) = constCut (a+c) 2 := by
  show cutHalf (cutSum (constCut a 1) (constCut c 1)) = constCut (a+c) 2
  rw [cutSum_int_int, cutHalf_constCut]

/-- **midpoint(a/1, c/2) = (2a+c)/4**. -/
theorem cutMid_int_half (a c : Nat) :
    cutMid (constCut a 1) (constCut c 2) = constCut (2*a+c) 4 := by
  show cutHalf (cutSum (constCut a 1) (constCut c 2)) = constCut (2*a+c) 4
  rw [cutSum_int_half, cutHalf_constCut]

/-- **midpoint(a/2, c/1) = (a+2c)/4**. -/
theorem cutMid_half_int (a c : Nat) :
    cutMid (constCut a 2) (constCut c 1) = constCut (a+2*c) 4 := by
  show cutHalf (cutSum (constCut a 2) (constCut c 1)) = constCut (a+2*c) 4
  rw [cutSum_half_int, cutHalf_constCut]

end E213.Research.Real213CutSum
