import E213.Lib.Math.Cohomology.Universal.Prop52
import E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 2) — corollary COH-2 template

Cochain 5 2 = Fin 10 → Bool, 1024 patterns × 10 indices = 10240
hodge ⋆⋆ evaluations.  Together with HodgeProp (5,1), establishes
the involution on the two physically meaningful strata of Δ⁴.
-/

namespace E213.Lib.Math.Cohomology.Hodge.Prop52

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar complementIdx)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
  (hodge_involution_pointwise_5)

private theorem c1_lt_binom3_5_2 :
    ∀ i : Fin (binom 5 2), complementIdx 5 2 i.val < binom 5 3 := by decide

private theorem c2_lt_binom2_5_2 :
    ∀ i : Fin (binom 5 2),
      complementIdx 5 3 (complementIdx 5 2 i.val) < binom 5 2 := by decide

private theorem c2_eq_i_5_2 :
    ∀ i : Fin (binom 5 2),
      complementIdx 5 3 (complementIdx 5 2 i.val) = i.val := by decide

/-- ★★★ Prop-level + Universal ⋆⋆=id capstone at (5, 2).  STRICT ∅-AXIOM
    via `hodge_involution_pointwise_5` template (G111 COH-2). -/
theorem hodge_sq_prop_5_2 (σ : Cochain 5 2) (i : Fin (binom 5 2)) :
    hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i :=
  hodge_involution_pointwise_5 2 3 σ i
    (c1_lt_binom3_5_2 i) (c2_lt_binom2_5_2 i) (c2_eq_i_5_2 i)

/-- Universal ⋆⋆=id Prop-lift capstone at (5, 2) — η-form. -/
theorem hodge_involution_capstone_5_2 :
    ∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i :=
  hodge_sq_prop_5_2

end E213.Lib.Math.Cohomology.Hodge.Prop52
