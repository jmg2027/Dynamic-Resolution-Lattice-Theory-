import E213.Research.Real213CutPow
import E213.Research.Real213CutMulOne

/-!
# Research.Real213CutPowConst: cutPow on const cuts

cutPow (constCut a b) 0 = 1, cutPow (constCut a b) 1 = (constCut a b).
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- (a/b)^1 = a/b for any a, b. -/
theorem cutPow_one_const (a b : Nat) :
    cutPow (constCut a b) 1 = constCut a b := cutMul_one_const a b

end E213.Research.Real213CutSum
