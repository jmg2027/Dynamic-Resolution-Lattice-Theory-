import E213.Lib.Math.Cohomology.Universal.Prop51
import E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 1) — corollary of G111 COH-2 template

User: hard deferred items 될때까지 고고.  Same pattern technique as
Universal δ²=0 lifts ⋆⋆ = id from concrete cochains to Prop-level ∀ σ.
-/

namespace E213.Lib.Math.Cohomology.Hodge.Prop

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar complementIdx)
open E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
  (hodge_involution_pointwise_5)

private theorem c1_lt_binom4_5_1 :
    ∀ i : Fin (binom 5 1), complementIdx 5 1 i.val < binom 5 4 := by decide

private theorem c2_lt_binom1_5_1 :
    ∀ i : Fin (binom 5 1),
      complementIdx 5 4 (complementIdx 5 1 i.val) < binom 5 1 := by decide

private theorem c2_eq_i_5_1 :
    ∀ i : Fin (binom 5 1),
      complementIdx 5 4 (complementIdx 5 1 i.val) = i.val := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 1, ⋆⋆σ = σ.  STRICT ∅-AXIOM via
    `hodge_involution_pointwise_5` template (G111 COH-2). -/
theorem hodge_sq_prop_5_1 (σ : Cochain 5 1) (i : Fin (binom 5 1)) :
    hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i :=
  hodge_involution_pointwise_5 1 4 σ i
    (c1_lt_binom4_5_1 i) (c2_lt_binom1_5_1 i) (c2_eq_i_5_1 i)

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 1).  STRICT ∅-AXIOM. -/
theorem hodge_involution_capstone :
    ∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
      hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i :=
  hodge_sq_prop_5_1

end E213.Lib.Math.Cohomology.Hodge.Prop
