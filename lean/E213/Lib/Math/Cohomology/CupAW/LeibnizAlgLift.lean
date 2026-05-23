import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftBeta

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Physics.Simplex.Counts
/-!
# Algebraic Leibniz lift framework — bilinearity-driven

`leibniz_via_β_decomp_lens`: given basis-component Leibniz at α
with each `bz5_2 β k`, derives universal (5, 1, 2) Leibniz via
the bilinearity lens.  Reduction is purely algebraic — no
kernel-decide blow-up.

Pipeline inside the proof:
  - rw `← decomp_5_2_eq` : substitute β by 10-term explicit sum
  - simp `cupAW_add_right_eq, delta_add_eq, h_components` :
    expand bilinearity + linearity, apply per-component Leibniz
  - apply `combine_10` (structural XOR rearrangement, 0-axiom) :
    close the residual 20-Bool combinatorial identity
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)

/-- ★ Bilinearity-driven Leibniz reduction at (5, 1, 2).  Now a
    1-line corollary of the parametric `leibniz_via_β_decomp_general`
    at `a = 1` ( L1). -/
theorem leibniz_via_β_decomp_lens
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3))
    (h_components : ∀ k : Fin 10,
      delta (cupAW 5 1 2 α (bz5_2 β k)) i
        = xor (cupAW 5 2 2 (delta α) (bz5_2 β k) i)
              (cupAW 5 1 3 α (delta (bz5_2 β k)) i)) :
    delta (cupAW 5 1 2 α β) i
      = xor (cupAW 5 2 2 (delta α) β i)
            (cupAW 5 1 3 α (delta β) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftBeta.leibniz_via_β_decomp_general
    α β i h_components

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift
