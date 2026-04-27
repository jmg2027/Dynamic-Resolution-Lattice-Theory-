import E213.Research.LensLattice

/-!
# Research.ConstLensTotalKernel: constLens 의 kernel = total
relation

PAPER1 §3.3 의 coarsest element claim 의 explicit:
constLens 의 equiv 가 모든 (x, y) 페어 위 true.
-/

namespace E213.Research.ConstLensTotalKernel

open E213.Firmware E213.Hypervisor
open E213.Research.LensLattice

/-- constLens 의 kernel: 모든 Raw pair 가 equivalent. -/
theorem constLens_equiv_total {α : Type} (e : α) (x y : Raw) :
    (constLens e).equiv x y := by
  unfold Lens.equiv
  rw [constLens_view, constLens_view]

end E213.Research.ConstLensTotalKernel
