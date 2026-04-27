import E213.Research.LensLattice
import E213.Research.LeavesRefinesParity

/-!
# Research.RefinesChain: Lens.refines preorder 의 explicit chain

PAPER1 §3.3 의 meet-semilattice claim 의 concrete witness:
finest (idLens) → ... → coarsest (constLens) 의 4-step
chain.

## Chain

```
idLens  →  Lens.leaves  →  parityLens  →  constLens true
(finest)                                      (coarsest)
```

Each arrow 가 strict refines.  반대 방향 은 strict (e.g.,
leaves 가 idLens 를 refine 하 지 않음 — leaves count 같지만
다른 Raw 들 존재).
-/

namespace E213.Research.RefinesChain

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

end E213.Research.RefinesChain
