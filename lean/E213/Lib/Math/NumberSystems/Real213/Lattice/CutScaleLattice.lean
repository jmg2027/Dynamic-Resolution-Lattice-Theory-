import E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection
import E213.Lib.Math.NumberSystems.Real213.Mul.CutDouble

import E213.Lib.Math.NumberSystems.Real213.Core.Core
/-!
# CutScaleLattice: cutHalf/cutDouble × cutMax/cutMin commute

These four commutation theorems are all rfl-trivial because
cutHalf and cutDouble shift independent slots (m or k) while
cutMax/cutMin are pointwise Bool operations.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Lattice.CutScaleLattice

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection (cutHalf)
open E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin (cutMax cutMin)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutDouble (cutDouble)

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

end E213.Lib.Math.NumberSystems.Real213.Lattice.CutScaleLattice
