import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftBeta

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Physics.Simplex.Counts
/-!
# Algebraic Leibniz lift at (5, 2, 2) — β-side and α-side lenses

Same bilinearity-lens technique as (5, 1, 2), specialised for
α : Cochain 5 2, β : Cochain 5 2.

Two lenses:
  - β-decomp: reduces (∀ α β) to per-component (∀ α, basis_q)
  - α-decomp (with β = basis q): reduces to per-component
    (basis_p, basis_q) — closed by `basis_leibniz_5_2_2`
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)

/-- ★ β-decomp lens at (5, 2, 2).  1-line corollary of
    `leibniz_via_β_decomp_general` at `a = 2` (G107 §3 L1). -/
theorem leibniz_via_β_decomp_22
    (α β : Cochain 5 2) (i : Fin (binom 5 4))
    (h_components : ∀ q : Fin 10,
      delta (cupAW 5 2 2 α (bz5_2 β q)) i
        = xor (cupAW 5 3 2 (delta α) (bz5_2 β q) i)
              (cupAW 5 2 3 α (delta (bz5_2 β q)) i)) :
    delta (cupAW 5 2 2 α β) i
      = xor (cupAW 5 3 2 (delta α) β i)
            (cupAW 5 2 3 α (delta β) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftBeta.leibniz_via_β_decomp_general
    α β i h_components

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22
