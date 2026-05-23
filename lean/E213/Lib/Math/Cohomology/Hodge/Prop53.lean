import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
import E213.Lib.Math.Cohomology.Universal.Prop53

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 3) — corollary COH-2 template

Cochain 5 3 = Fin (binom 5 3) → Bool = Fin 10 → Bool, 1024
patterns × 10 indices = 10240 evaluations.  Same scale as (5, 2).

Closes the second-from-top stratum of the Hodge involution chain.
-/

namespace E213.Lib.Math.Cohomology.Hodge.Prop53

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar complementIdx)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
  (hodge_involution_pointwise_5)

private theorem c1_lt_binom2_5_3 :
    ∀ i : Fin (binom 5 3), complementIdx 5 3 i.val < binom 5 2 := by decide

private theorem c2_lt_binom3_5_3 :
    ∀ i : Fin (binom 5 3),
      complementIdx 5 2 (complementIdx 5 3 i.val) < binom 5 3 := by decide

private theorem c2_eq_i_5_3 :
    ∀ i : Fin (binom 5 3),
      complementIdx 5 2 (complementIdx 5 3 i.val) = i.val := by decide

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 3).  STRICT ∅-AXIOM
    via `hodge_involution_pointwise_5` template (G111 COH-2). -/
theorem hodge_involution_capstone_5_3 :
    ∀ σ : Cochain 5 3, ∀ i : Fin (binom 5 3),
      hodgeStar 5 2 3 (hodgeStar 5 3 2 σ) i = σ i :=
  fun σ i => hodge_involution_pointwise_5 3 2 σ i
    (c1_lt_binom2_5_3 i) (c2_lt_binom3_5_3 i) (c2_eq_i_5_3 i)

end E213.Lib.Math.Cohomology.Hodge.Prop53
