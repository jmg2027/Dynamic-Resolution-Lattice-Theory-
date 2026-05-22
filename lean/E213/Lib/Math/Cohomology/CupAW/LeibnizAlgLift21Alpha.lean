import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftAlpha

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Algebraic Leibniz lift at (5, 2, 1) — α-side lens (b=1 corollary)

Thin corollary of `LeibnizAlgLiftAlpha.leibniz_via_α_decomp_general`
at `b = 1`.  At that value the `castA`/`castB` casts in the general
helper's signature reduce to identity (both index types become
`Fin (binom 5 3)`), so the user's `h_components` (no cast) matches
directly.
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)

/-- ★ α-decomp lens at (5, 2, 1).  PURE.  Corollary of
    `LeibnizAlgLiftAlpha.leibniz_via_α_decomp_general` at `b=1`. -/
theorem leibniz_via_α_decomp_21
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3))
    (h_components : ∀ p : Fin 10,
      delta (cupAW 5 2 1 (bz5_2 α p) β) i
        = xor (cupAW 5 3 1 (delta (bz5_2 α p)) β i)
              (cupAW 5 2 2 (bz5_2 α p) (delta β) i)) :
    delta (cupAW 5 2 1 α β) i
      = xor (cupAW 5 3 1 (delta α) β i)
            (cupAW 5 2 2 α (delta β) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftAlpha.leibniz_via_α_decomp_general
    α β i h_components

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha
