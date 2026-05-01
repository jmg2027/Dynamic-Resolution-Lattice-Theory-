import E213.Research.Lens.Lattice
import E213.Research.Leaves.RefinesParity

/-!
# Research.RefinesChain: explicit chain in the Lens.refines preorder

Concrete witness for the meet-semilattice claim in PAPER1 §3.3:
4-step chain from finest (idLens) → ... → coarsest (constLens).

## Chain

```
idLens  →  Lens.leaves  →  parityLens  →  constLens true
(finest)                                      (coarsest)
```

Each arrow is a strict refinement.  The reverse direction is strict (e.g.,
leaves does not refine idLens — leaf counts agree but different Raws exist).
-/

namespace E213.Research.Refines.Chain

open E213.Firmware E213.Hypervisor
open E213.Meta
open E213.Research.IdentityLens
open E213.Research.LensLattice
open E213.Research.LeavesRefinesParity

/-- **4-step chain**: idLens → leaves → parity → constLens true. -/
theorem refines_chain :
    idLens.refines Lens.leaves ∧
    Lens.leaves.refines parityLens ∧
    parityLens.refines (constLens (true : Bool)) :=
  ⟨idLens_refines_all Lens.leaves,
   leaves_refines_parity,
   all_refine_constLens true parityLens⟩

end E213.Research.Refines.Chain
