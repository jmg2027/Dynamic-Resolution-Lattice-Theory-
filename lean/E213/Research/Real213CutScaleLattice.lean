import E213.Research.Real213CutMaxMin
import E213.Research.Real213CutBisection
import E213.Research.Real213CutDouble

/-!
# Research.Real213CutScaleLattice: cutHalf/cutDouble × cutMax/cutMin commute

These four commutation theorems are all rfl-trivial because
cutHalf and cutDouble shift independent slots (m or k) while
cutMax/cutMin are pointwise Bool operations.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- cutHalf distributes over cutMax. -/
theorem cutHalf_cutMax (cx cy : Nat → Nat → Bool) :
    cutHalf (cutMax cx cy) = cutMax (cutHalf cx) (cutHalf cy) := rfl

/-- cutHalf distributes over cutMin. -/
theorem cutHalf_cutMin (cx cy : Nat → Nat → Bool) :
    cutHalf (cutMin cx cy) = cutMin (cutHalf cx) (cutHalf cy) := rfl

/-- cutDouble distributes over cutMax. -/
theorem cutDouble_cutMax (cx cy : Nat → Nat → Bool) :
    cutDouble (cutMax cx cy) = cutMax (cutDouble cx) (cutDouble cy) := rfl

/-- cutDouble distributes over cutMin. -/
theorem cutDouble_cutMin (cx cy : Nat → Nat → Bool) :
    cutDouble (cutMin cx cy) = cutMin (cutDouble cx) (cutDouble cy) := rfl

end E213.Research.Real213CutSum
