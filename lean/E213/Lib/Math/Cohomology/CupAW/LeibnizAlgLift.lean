import E213.Lib.Math.Cohomology.CupAW.BilinearFunc
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.XorPairCombine

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Delta.Linear
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# Algebraic Leibniz lift framework — bilinearity-driven

`leibniz_via_β_decomp_lens`: given basis-component Leibniz at α
with each `bz5_2 β k`, derives universal (5, 1, 2) Leibniz via
the bilinearity lens.  Reduction is purely algebraic — no
kernel-decide blow-up.

Pipeline inside the proof:
  - rw `← decomp_5_2_eq` : substitute β by 10-term explicit sum
  - simp `cupAW_add_right_eq, delta_add_eq, h_components` :
    expand bilinearity + linearity, apply per-component Leibniz
  - apply `combine_10` (structural XOR rearrangement, 0-axiom) :
    close the residual 20-Bool combinatorial identity
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (decomp_5_2 decomp_5_2_eq)
open E213.Lib.Math.Cohomology.XorPairCombine (combine_10)
open E213.Lib.Math.Cohomology.CupAW.BilinearFunc (cupAW_add_right_eq cupAW_add_left_eq delta_add_eq)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left cupAW_add_right)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)

/-- ★ Bilinearity-driven Leibniz reduction at (5, 1, 2). -/
theorem leibniz_via_β_decomp_lens
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3))
    (h_components : ∀ k : Fin 10,
      delta (cupAW 5 1 2 α
        (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β k)) i
        = xor (cupAW 5 2 2 (delta α)
                (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β k) i)
              (cupAW 5 1 3 α
                (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β k)) i)) :
    delta (cupAW 5 1 2 α β) i
      = xor (cupAW 5 2 2 (delta α) β i)
            (cupAW 5 1 3 α (delta β) i) := by
  rw [← decomp_5_2_eq β]
  unfold decomp_5_2
  simp only [cupAW_add_right_eq, delta_add_eq,
             cupAW_add_right, delta_add, h_components]
  exact combine_10
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨0, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨1, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨2, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨3, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨4, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨5, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨6, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨7, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨8, by decide⟩) i)
    (cupAW 5 2 2 (delta α) (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨9, by decide⟩) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨0, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨1, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨2, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨3, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨4, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨5, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨6, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨7, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨8, by decide⟩)) i)
    (cupAW 5 1 3 α (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β ⟨9, by decide⟩)) i)

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift
