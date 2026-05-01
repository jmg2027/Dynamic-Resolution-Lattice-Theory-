import E213.Research.Morphism.FoldStructured
import E213.Research.Morphism.NoDepthParity

/-!
# Research.DepthParityNotFold: depth parity function is not fold-structured

`fun r => decide (Lens.depth.view r % 2 = 1)` — this Raw → Bool
function is **not** fold-structured.

Therefore no Bool-valued Lens can have this function as its view
(by the FoldStructured iff Lens-expressible equivalence).

Positive version of `NoDepthParity`: the partition is not a
slash-congruence ⟺ the function is not fold-structured.

Concrete application of both perspectives (note 42 §1).
-/

namespace E213.Research.DepthParityNotFold

open E213.Firmware E213.Hypervisor
open E213.Research.FoldStructured E213.Research.NoDepthParity

/-- The depth parity function. -/
def depthParityFn (r : Raw) : Bool :=
  decide (Lens.depth.view r % 2 = 1)

private theorem depthParityFn_rA1 : depthParityFn rA1 = true := by decide
private theorem depthParityFn_rA3 : depthParityFn rA3 = true := by decide
private theorem depthParityFn_rB2 : depthParityFn rB2 = false := by decide

private theorem depthParityFn_slash12 : depthParityFn slash12 = true := by decide
private theorem depthParityFn_slash32 : depthParityFn slash32 = false := by decide

/-- **The depth parity function is not fold-structured**. -/
theorem depthParityFn_not_fold_structured :
    ¬ FoldStructured depthParityFn := by
  intro ⟨ba, bb, c, _, _, _, hslash⟩
  -- From fold structure:
  -- depthParityFn (slash rA1 rB2 _) = c (depthParityFn rA1) (depthParityFn rB2)
  -- depthParityFn (slash rA3 rB2 _) = c (depthParityFn rA3) (depthParityFn rB2)
  -- Both call c true false, so same result. But actually different.
  have h12 : depthParityFn slash12
               = c (depthParityFn rA1) (depthParityFn rB2) :=
    hslash rA1 rB2 _
  have h32 : depthParityFn slash32
               = c (depthParityFn rA3) (depthParityFn rB2) :=
    hslash rA3 rB2 _
  rw [depthParityFn_rA1, depthParityFn_rB2, depthParityFn_slash12] at h12
  rw [depthParityFn_rA3, depthParityFn_rB2, depthParityFn_slash32] at h32
  -- h12 : true = c true false, h32 : false = c true false
  rw [← h12] at h32
  cases h32

end E213.Research.DepthParityNotFold
