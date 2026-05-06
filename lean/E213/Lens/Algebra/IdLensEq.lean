import E213.Lens.Instances.Identity

/-!
# IdLensKernelEq: idLens.equiv = equality

`idLens` is the finest Lens — its kernel is exactly `=` on Raw.
Explicit theorem for the finest element claim of PAPER1 §3.3.
-/

namespace E213.Lens.Algebra.IdLensEq

open E213.Theory E213.Lens
open E213.Lens.Instances.Identity

/-- The kernel of idLens is exactly equality on Raw. -/
theorem idLens_equiv_eq (x y : Raw) : idLens.equiv x y ↔ x = y := by
  unfold Lens.equiv
  rw [idLens_is_id, idLens_is_id]

end E213.Lens.Algebra.IdLensEq
