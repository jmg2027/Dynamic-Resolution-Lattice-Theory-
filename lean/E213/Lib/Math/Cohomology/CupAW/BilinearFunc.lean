import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.Delta.Linear

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
/-!
# Function-level versions of bilinearity / linearity (deprecated)

Originally housed the funext-based `cupAW_add_*_eq` and `delta_add_eq`
function-level lemmas, used by the simp-only chains in
`LeibnizAlgLift*` proofs.  After the LeibnizAlgLift family was
refactored to PURE (pointwise lifts via `cupAW_pointwise_eq` and
`delta_pointwise_eq`), those funext bridges had no remaining
consumers and were deleted (each was `[Quot.sound]`-DIRTY by funext,
Cat 1 inherent).

This file is kept (with no public theorems) only to preserve the
import graph; the `CupAW.lean` aggregator still references it.
Use `CupAW/Pointwise.lean`, `Delta/Pointwise.lean`, and
`CupAW/PointwiseBilinear.lean` for the PURE replacements.
-/

namespace E213.Lib.Math.Cohomology.CupAW.BilinearFunc

end E213.Lib.Math.Cohomology.CupAW.BilinearFunc
