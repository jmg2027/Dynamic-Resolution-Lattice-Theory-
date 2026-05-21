import E213.Lib.Math.Cohomology.Hodge.Star

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 4) — Δ⁴ 4-cochain (Hodge dual of (5, 1))

Cochain 5 4 = Fin (binom 5 4) → Bool = Fin 5 → Bool, 32 functions.
By Hodge duality, the structure is identical to (5, 1):
binom 5 4 = binom 5 1 = 5.  ⋆⋆ : C⁴ → C⁴ is computed via
⋆ : C⁴ → C¹ → ⋆ : C¹ → C⁴.

Closes the top-1 stratum of the Hodge involution chain.
32 patterns × 5 indices = 160 evaluations.
-/

namespace E213.Lib.Math.Cohomology.Hodge.Prop54

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar)

open E213.Lib.Physics.Simplex.Counts (binom)

open E213.Lib.Math.Cohomology.Hodge.Star (complementIdx)

private theorem c1_lt_binom1_5_4 :
    ∀ i : Fin (binom 5 4), complementIdx 5 4 i.val < binom 5 1 := by decide

private theorem c2_lt_binom4_5_4 :
    ∀ i : Fin (binom 5 4),
      complementIdx 5 1 (complementIdx 5 4 i.val) < binom 5 4 := by decide

private theorem c2_eq_i_5_4 :
    ∀ i : Fin (binom 5 4),
      complementIdx 5 1 (complementIdx 5 4 i.val) = i.val := by decide

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 4).  STRICT ∅-AXIOM. -/
theorem hodge_involution_capstone_5_4 :
    ∀ σ : Cochain 5 4, ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i := by
  intro σ i
  show (if h : complementIdx 5 4 i.val < binom 5 1 then
          (hodgeStar 5 4 1 σ) ⟨complementIdx 5 4 i.val, h⟩
        else false) = σ i
  rw [dif_pos (c1_lt_binom1_5_4 i)]
  show (if h : complementIdx 5 1 (complementIdx 5 4 i.val) < binom 5 4 then
          σ ⟨complementIdx 5 1 (complementIdx 5 4 i.val), h⟩
        else false) = σ i
  rw [dif_pos (c2_lt_binom4_5_4 i)]
  exact congrArg σ (Fin.ext (c2_eq_i_5_4 i))

end E213.Lib.Math.Cohomology.Hodge.Prop54
