import E213.Math.Cohomology.Universal.Prop51

import E213.Math.Cohomology.Cochain.Core
import E213.Math.Cohomology.Hodge.Star
import E213.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 1) and (5, 2)

User: hard deferred items 될때까지 고고.  Same pattern
technique as Universal δ²=0 lifts ⋆⋆ = id from concrete
cochains to Prop-level ∀ σ.
-/

namespace E213.Math.Cohomology.Hodge.Prop

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)

open E213.Math.Cohomology.Hodge.Star (complementIdx)

/-- Outer condition: c1 = complementIdx 5 1 i.val < binom 5 4. -/
private theorem c1_lt_binom4_5_1 :
    ∀ i : Fin (binom 5 1), complementIdx 5 1 i.val < binom 5 4 := by decide

/-- Inner condition: complementIdx 5 4 c1 < binom 5 1. -/
private theorem c2_lt_binom1_5_1 :
    ∀ i : Fin (binom 5 1),
      complementIdx 5 4 (complementIdx 5 1 i.val) < binom 5 1 := by decide

/-- ⋆⋆ pointwise involution: c2 = i. -/
private theorem c2_eq_i_5_1 :
    ∀ i : Fin (binom 5 1),
      complementIdx 5 4 (complementIdx 5 1 i.val) = i.val := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 1, ⋆⋆σ = σ.  STRICT ∅-AXIOM. -/
theorem hodge_sq_prop_5_1 (σ : Cochain 5 1)
    (i : Fin (binom 5 1)) :
    hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i := by
  show (if h : complementIdx 5 1 i.val < binom 5 4 then
          (hodgeStar 5 1 4 σ) ⟨complementIdx 5 1 i.val, h⟩
        else false) = σ i
  rw [dif_pos (c1_lt_binom4_5_1 i)]
  show (if h : complementIdx 5 4 (complementIdx 5 1 i.val) < binom 5 1 then
          σ ⟨complementIdx 5 4 (complementIdx 5 1 i.val), h⟩
        else false) = σ i
  rw [dif_pos (c2_lt_binom1_5_1 i)]
  exact congrArg σ (Fin.ext (c2_eq_i_5_1 i))

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 1).  STRICT ∅-AXIOM. -/
theorem hodge_involution_capstone :
    ∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
      hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i :=
  hodge_sq_prop_5_1

end E213.Math.Cohomology.Hodge.Prop
