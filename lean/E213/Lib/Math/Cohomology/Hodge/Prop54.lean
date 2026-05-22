import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 4) — corollary of G111 COH-2 template

Cochain 5 4 = Fin (binom 5 4) → Bool = Fin 5 → Bool, 32 functions.
By Hodge duality, the structure is identical to (5, 1):
binom 5 4 = binom 5 1 = 5.  ⋆⋆ : C⁴ → C⁴ is computed via
⋆ : C⁴ → C¹ → ⋆ : C¹ → C⁴.
-/

namespace E213.Lib.Math.Cohomology.Hodge.Prop54

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar complementIdx)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
  (hodge_involution_pointwise_5)

private theorem c1_lt_binom1_5_4 :
    ∀ i : Fin (binom 5 4), complementIdx 5 4 i.val < binom 5 1 := by decide

private theorem c2_lt_binom4_5_4 :
    ∀ i : Fin (binom 5 4),
      complementIdx 5 1 (complementIdx 5 4 i.val) < binom 5 4 := by decide

private theorem c2_eq_i_5_4 :
    ∀ i : Fin (binom 5 4),
      complementIdx 5 1 (complementIdx 5 4 i.val) = i.val := by decide

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 4).  STRICT ∅-AXIOM
    via `hodge_involution_pointwise_5` template (G111 COH-2). -/
theorem hodge_involution_capstone_5_4 :
    ∀ σ : Cochain 5 4, ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i :=
  fun σ i => hodge_involution_pointwise_5 4 1 σ i
    (c1_lt_binom1_5_4 i) (c2_lt_binom4_5_4 i) (c2_eq_i_5_4 i)

end E213.Lib.Math.Cohomology.Hodge.Prop54
