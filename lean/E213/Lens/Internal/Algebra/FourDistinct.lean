import E213.Lens.Instances.Identity

/-!
# FourDistinctKernels: explicit kernel pair distinctness

Multiple-element witness for the Lens-kernel space in PAPER1 §5.4:
{idLens, Lens.leaves} have distinct kernels.

## Core

Witness: `Raw.a, Raw.b` — same leaf count (both 1) but Raw.a ≠ Raw.b.
Therefore leaves-equiv, but idLens is not-equiv.
-/

namespace E213.Lens.Internal.Algebra.FourDistinct

open E213.Theory E213.Lens
open E213.Lens.Instances.Identity

/-- Kernels of idLens and Lens.leaves are pairwise distinct.
    Witness pair (Raw.a, Raw.b): same leaves count (both 1)
    but idLens distinguishes them (Raw.a ≠ Raw.b). -/
theorem id_neq_leaves :
    Lens.leaves.equiv Raw.a Raw.b ∧ ¬ idLens.equiv Raw.a Raw.b := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro h
    have hab : Raw.a = Raw.b := by
      rw [← idLens_is_id Raw.a, ← idLens_is_id Raw.b]; exact h
    exact (by decide : (Raw.a : Raw) ≠ Raw.b) hab

end E213.Lens.Internal.Algebra.FourDistinct
