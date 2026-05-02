import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutSumEq

/-!
# Research.Real213CutMidEq: cutMid preserves cutEq + cutLe

cutMid = cutHalf ∘ cutSum, so cutEq/cutLe compatibility lifts from
cutSum (cutSum_cutEq_left/right etc.) by composition.
-/

namespace E213.Math.Real213.CutMidEq

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutPoset (cutEq cutEq_trans cutLe cutLe_trans)

/-- cutMid preserves cutEq on left arg. -/
theorem cutMid_cutEq_left (cx cx' cy : Nat → Nat → Bool)
    (h : cutEq cx cx') :
    cutEq (cutMid cx cy) (cutMid cx' cy) := fun m k => by
  show cutSum cx cy (2*m) k = cutSum cx' cy (2*m) k
  exact cutSum_cutEq_left cx cx' cy h (2*m) k

/-- cutMid preserves cutEq on right arg. -/
theorem cutMid_cutEq_right (cx cy cy' : Nat → Nat → Bool)
    (h : cutEq cy cy') :
    cutEq (cutMid cx cy) (cutMid cx cy') := fun m k => by
  show cutSum cx cy (2*m) k = cutSum cx cy' (2*m) k
  exact cutSum_cutEq_right cx cy cy' h (2*m) k

/-- cutMid preserves cutEq on both args. -/
theorem cutMid_cutEq_both (cx cx' cy cy' : Nat → Nat → Bool)
    (hx : cutEq cx cx') (hy : cutEq cy cy') :
    cutEq (cutMid cx cy) (cutMid cx' cy') :=
  cutEq_trans _ _ _ (cutMid_cutEq_left cx cx' cy hx)
                    (cutMid_cutEq_right cx' cy cy' hy)

/-- cutMid preserves cutLe on left arg. -/
theorem cutMid_cutLe_left (cx1 cx2 cy : Nat → Nat → Bool)
    (h : cutLe cx1 cx2) :
    cutLe (cutMid cx1 cy) (cutMid cx2 cy) := fun m k h_mid => by
  show cutSum cx1 cy (2*m) k = true
  exact cutSum_cutLe_left cx1 cx2 cy h (2*m) k h_mid

/-- cutMid preserves cutLe on right arg. -/
theorem cutMid_cutLe_right (cx cy1 cy2 : Nat → Nat → Bool)
    (h : cutLe cy1 cy2) :
    cutLe (cutMid cx cy1) (cutMid cx cy2) := fun m k h_mid => by
  show cutSum cx cy1 (2*m) k = true
  exact cutSum_cutLe_right cx cy1 cy2 h (2*m) k h_mid

/-- cutMid preserves cutLe on both args. -/
theorem cutMid_cutLe_both (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : cutLe cx1 cx2) (hy : cutLe cy1 cy2) :
    cutLe (cutMid cx1 cy1) (cutMid cx2 cy2) :=
  cutLe_trans _ _ _ (cutMid_cutLe_left cx1 cx2 cy1 hx)
                    (cutMid_cutLe_right cx2 cy1 cy2 hy)

end E213.Math.Real213.CutMidEq
