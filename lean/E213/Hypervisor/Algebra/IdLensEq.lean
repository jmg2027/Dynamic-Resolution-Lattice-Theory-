import E213.Hypervisor.Instances.Identity

/-!
# IdLensKernelEq: idLens.equiv = equality

`idLens` is the finest Lens — its kernel is exactly `=` on Raw.
Explicit theorem for the finest element claim of PAPER1 §3.3.
-/

namespace E213.Hypervisor.Algebra.IdLensEq

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Instances.Identity

/-- The kernel of idLens is exactly equality on Raw. -/
theorem idLens_equiv_eq (x y : Raw) : idLens.equiv x y ↔ x = y := by
  unfold Lens.equiv
  rw [idLens_is_id, idLens_is_id]

end E213.Hypervisor.Algebra.IdLensEq
