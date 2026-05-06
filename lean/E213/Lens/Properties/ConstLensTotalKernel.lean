import E213.Lens.Lattice.Lattice

/-!
# ConstLensTotalKernel: kernel of constLens = total relation

Explicit version of the coarsest element claim in PAPER1 §3.3:
constLens's equiv is true for every (x, y) pair.
-/

namespace E213.Lens.Properties.ConstLensTotalKernel

open E213.Theory E213.Lens
open E213.Lens.Lattice.Lattice

/-- Kernel of constLens: every Raw pair is equivalent. -/
theorem constLens_equiv_total {α : Type} (e : α) (x y : Raw) :
    (constLens e).equiv x y := by
  unfold Lens.equiv
  rw [constLens_view, constLens_view]

end E213.Lens.Properties.ConstLensTotalKernel
