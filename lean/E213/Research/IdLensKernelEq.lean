import E213.Research.IdentityLens

/-!
# Research.IdLensKernelEq: idLens.equiv = equality

`idLens` 가 finest Lens — 그 kernel 이 정확 히 `=` on Raw.
PAPER1 §3.3 의 finest element claim 의 explicit theorem.
-/

namespace E213.Research.IdLensKernelEq

open E213.Firmware E213.Hypervisor
open E213.Research.IdentityLens

/-- idLens 의 kernel 이 정확 히 Raw 동등성. -/
theorem idLens_equiv_eq (x y : Raw) : idLens.equiv x y ↔ x = y := by
  unfold Lens.equiv
  rw [idLens_is_id, idLens_is_id]

end E213.Research.IdLensKernelEq
