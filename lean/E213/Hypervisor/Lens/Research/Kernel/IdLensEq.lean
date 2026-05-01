import E213.Hypervisor.Lens.Research.Lens.Identity

/-!
# Research.IdLensKernelEq: idLens.equiv = equality

`idLens` is the finest Lens — its kernel is exactly `=` on Raw.
Explicit theorem for the finest element claim of PAPER1 §3.3.
-/

namespace E213.Hypervisor.Lens.Research.Kernel.IdLensEq

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.Lens.Identity

/-- The kernel of idLens is exactly equality on Raw. -/
theorem idLens_equiv_eq (x y : Raw) : idLens.equiv x y ↔ x = y := by
  unfold Lens.equiv
  rw [idLens_is_id, idLens_is_id]

end E213.Hypervisor.Lens.Research.Kernel.IdLensEq
