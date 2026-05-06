import E213.Hypervisor.Lattice.Lattice

/-!
# ConstLensTotalKernel: kernel of constLens = total relation

Explicit version of the coarsest element claim in PAPER1 §3.3:
constLens's equiv is true for every (x, y) pair.
-/

namespace E213.Hypervisor.Properties.ConstLensTotalKernel

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lattice.Lattice

/-- Kernel of constLens: every Raw pair is equivalent. -/
theorem constLens_equiv_total {α : Type} (e : α) (x y : Raw) :
    (constLens e).equiv x y := by
  unfold Lens.equiv
  rw [constLens_view, constLens_view]

end E213.Hypervisor.Properties.ConstLensTotalKernel
