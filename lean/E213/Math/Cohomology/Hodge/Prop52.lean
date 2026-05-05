import E213.Math.Cohomology.Universal.Prop52

import E213.Math.Cohomology.Cochain.Core
import E213.Math.Cohomology.Hodge.Star
import E213.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 2) — Δ⁴ edge cochain involution

Cochain 5 2 = Fin 10 → Bool, 1024 patterns × 10 indices = 10240
hodge ⋆⋆ evaluations.  Together with HodgeProp (5,1), establishes
the involution on the two physically meaningful strata of Δ⁴:
vertex (5,1) and edge (5,2) cochains.
-/

namespace E213.Math.Cohomology.Hodge.Prop52

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)

open E213.Physics.Simplex.Counts (binom)

open E213.Math.Cohomology.Hodge.Star (complementIdx)

private theorem c1_lt_binom3_5_2 :
    ∀ i : Fin (binom 5 2), complementIdx 5 2 i.val < binom 5 3 := by decide

private theorem c2_lt_binom2_5_2 :
    ∀ i : Fin (binom 5 2),
      complementIdx 5 3 (complementIdx 5 2 i.val) < binom 5 2 := by decide

private theorem c2_eq_i_5_2 :
    ∀ i : Fin (binom 5 2),
      complementIdx 5 3 (complementIdx 5 2 i.val) = i.val := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 2, ⋆⋆σ = σ.  STRICT ∅-AXIOM. -/
theorem hodge_sq_prop_5_2 (σ : Cochain 5 2)
    (i : Fin (binom 5 2)) :
    hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i := by
  show (if h : complementIdx 5 2 i.val < binom 5 3 then
          (hodgeStar 5 2 3 σ) ⟨complementIdx 5 2 i.val, h⟩
        else false) = σ i
  rw [dif_pos (c1_lt_binom3_5_2 i)]
  show (if h : complementIdx 5 3 (complementIdx 5 2 i.val) < binom 5 2 then
          σ ⟨complementIdx 5 3 (complementIdx 5 2 i.val), h⟩
        else false) = σ i
  rw [dif_pos (c2_lt_binom2_5_2 i)]
  exact congrArg σ (Fin.ext (c2_eq_i_5_2 i))

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 2).  STRICT ∅-AXIOM. -/
theorem hodge_involution_capstone_5_2 :
    ∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i :=
  hodge_sq_prop_5_2

end E213.Math.Cohomology.Hodge.Prop52
