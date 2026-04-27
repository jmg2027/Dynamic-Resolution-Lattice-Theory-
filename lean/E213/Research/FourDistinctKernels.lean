import E213.Research.IdentityLens

/-!
# Research.FourDistinctKernels: explicit kernel pair distinctness

PAPER1 §5.4 의 Lens-kernel space 의 multiple-element witness:
{idLens, Lens.leaves} 가 distinct kernels.

## 핵심

Witness: `Raw.a, Raw.b` — leaves count 같음 (둘 다 1) 이지만
Raw.a ≠ Raw.b.  따라서 leaves equiv 인데 idLens 는 not equiv.
-/

namespace E213.Research.FourDistinctKernels

open E213.Firmware E213.Hypervisor
open E213.Research.IdentityLens

/-- idLens 와 Lens.leaves 의 kernel pairwise distinct.
    Witness pair (Raw.a, Raw.b): leaves 같지만 (둘 다 1)
    idLens 는 다름 (Raw.a ≠ Raw.b). -/
theorem id_neq_leaves :
    Lens.leaves.equiv Raw.a Raw.b ∧ ¬ idLens.equiv Raw.a Raw.b := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro h
    have hab : Raw.a = Raw.b := by
      rw [← idLens_is_id Raw.a, ← idLens_is_id Raw.b]; exact h
    exact (by decide : (Raw.a : Raw) ≠ Raw.b) hab

end E213.Research.FourDistinctKernels
