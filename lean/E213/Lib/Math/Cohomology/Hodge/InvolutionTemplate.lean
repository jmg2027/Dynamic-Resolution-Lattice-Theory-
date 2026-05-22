import E213.Lib.Math.Cohomology.Hodge.Star

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Hodge ⋆⋆ = id involution template — G111 COH-2 (Hodge Prop quartet)

The 4 `hodge_sq_prop_5_k` proofs (k ∈ {1, 2, 3, 4}) in
`Hodge/Prop.lean`, `Prop52.lean`, `Prop53.lean`, `Prop54.lean` follow
byte-identical structure: two `dif_pos` rewrites + `congrArg σ ∘
Fin.ext` closure.  The variable parts are just the three per-(k,d)
`decide`-checked complement bounds + equality.

`hodge_involution_pointwise_5` packages that proof skeleton; the four
files become 1-line corollaries.
-/

namespace E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar complementIdx)

/-- ★ Generic Hodge ⋆⋆=id pointwise involution at n=5, for any
    `(k, d)` pair with `d = 5-k` semantically.  PURE.  Caller supplies
    the three `decide`-checkable facts about `complementIdx`. -/
theorem hodge_involution_pointwise_5
    (k d : Nat) (σ : Cochain 5 k) (i : Fin (binom 5 k))
    (h_c1 : complementIdx 5 k i.val < binom 5 d)
    (h_c2 : complementIdx 5 d (complementIdx 5 k i.val) < binom 5 k)
    (h_c_eq : complementIdx 5 d (complementIdx 5 k i.val) = i.val) :
    hodgeStar 5 d k (hodgeStar 5 k d σ) i = σ i := by
  show (if h : complementIdx 5 k i.val < binom 5 d then
          (hodgeStar 5 k d σ) ⟨complementIdx 5 k i.val, h⟩
        else false) = σ i
  rw [dif_pos h_c1]
  show (if h : complementIdx 5 d (complementIdx 5 k i.val) < binom 5 k then
          σ ⟨complementIdx 5 d (complementIdx 5 k i.val), h⟩
        else false) = σ i
  rw [dif_pos h_c2]
  exact congrArg σ (Fin.ext h_c_eq)

end E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
