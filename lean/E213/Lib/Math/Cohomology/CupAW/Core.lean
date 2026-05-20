import E213.Lib.Math.Cohomology.Cup.Core

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Physics.Simplex.Counts
/-!
# Alexander–Whitney cup with overlap (cupAW)

Per `LeibnizFinding.lean`, the original `cup` uses split convention
`τ.take k / τ.drop k` (no overlap), which makes universal Leibniz
fail.  Standard simplicial AW cup uses overlap at the shared vertex
`v_{a-1}`:

  cupAW n a b α β τ := α(τ.take a) · β(τ.drop (a-1))
  type:  Cochain n a × Cochain n b → Cochain n (a+b-1)

Our `Cochain n k` reads k-element subsets as Bool-functions on
those subsets.  Degree-sum (a+b−1) is the AW overlap convention
applied to this indexing — input arities a, b ≥ 1 and output
a+b−1 ≥ 1.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Core

open E213.Lib.Physics.Simplex.Counts (binom d NS NT)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Cup.Core (cup)

/-- Alexander–Whitney cup with overlap at v_{a-1}. -/
def cupAW (n a b : Nat) (α : Cochain n a) (β : Cochain n b) :
    Cochain n (a + b - 1) :=
  fun τ_idx =>
    let τ := kSubset n (a + b - 1) τ_idx.val
    let front := τ.take a
    let back := τ.drop (a - 1)
    let f_idx := subsetIdx n a front
    let b_idx := subsetIdx n b back
    if hf : f_idx < binom n a then
      if hb : b_idx < binom n b then
        α ⟨f_idx, hf⟩ && β ⟨b_idx, hb⟩
      else false
    else false

/-- Smoke: cupAW with zero left = zero (vertex × vertex). -/
theorem cupAW_zero_left_5_1_1 :
    ∀ i : Fin (binom 5 1),
      cupAW 5 1 1 (Cochain.zero 5 1) v0_5 i = false := by decide

/-- Smoke: cupAW v0 ⌣ v0 — overlaps at vertex 0, picks up
    only the diagonal subset {0}. -/
theorem cupAW_v0_v0_at_0 :
    cupAW 5 1 1 v0_5 v0_5 ⟨0, by decide⟩ = true := by decide

/-- Smoke: cupAW v0 ⌣ v0 at any other vertex j ≠ 0 = false. -/
theorem cupAW_v0_v0_off_diagonal :
    cupAW 5 1 1 v0_5 v0_5 ⟨1, by decide⟩ = false := by decide

/-- ★ AW cup product smoke capstone — well-defined and matches
    overlap convention at the diagonal. -/
theorem cupAW_smoke_capstone :
    cupAW 5 1 1 v0_5 v0_5 ⟨0, by decide⟩ = true
    ∧ cupAW 5 1 1 v0_5 v0_5 ⟨1, by decide⟩ = false
    ∧ (∀ i : Fin (binom 5 1),
         cupAW 5 1 1 (Cochain.zero 5 1) v0_5 i = false) :=
  ⟨cupAW_v0_v0_at_0, cupAW_v0_v0_off_diagonal,
   cupAW_zero_left_5_1_1⟩

end E213.Lib.Math.Cohomology.CupAW.Core
