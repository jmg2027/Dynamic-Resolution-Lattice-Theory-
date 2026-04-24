import E213.Research.FoldStructured
import E213.Research.NoDepthParity

/-!
# Research.DepthParityNotFold: depth parity 함수는 fold-structured 가 아님

`fun r => decide (Lens.depth.view r % 2 = 1)` — 이 Raw → Bool
함수는 fold-structured 가 **아님**.

따라서 어떤 Bool-valued Lens 도 이 함수를 view 로 가질 수 없음
(FoldStructured iff Lens-expressible 에 의해).

`NoDepthParity` 의 positive version: partition 가 slash-congruence
아님 ⟺ 함수가 fold-structured 아님.

두 관점 (note 42 §1) 의 concrete 적용.
-/

namespace E213.Research.DepthParityNotFold

open E213.Firmware E213.Hypervisor
open E213.Research.FoldStructured E213.Research.NoDepthParity

/-- depth parity 함수. -/
def depthParityFn (r : Raw) : Bool :=
  decide (Lens.depth.view r % 2 = 1)

private theorem depthParityFn_rA1 : depthParityFn rA1 = true := by decide
private theorem depthParityFn_rA3 : depthParityFn rA3 = true := by decide
private theorem depthParityFn_rB2 : depthParityFn rB2 = false := by decide

private theorem depthParityFn_slash12 : depthParityFn slash12 = true := by decide
private theorem depthParityFn_slash32 : depthParityFn slash32 = false := by decide

/-- **depth parity 함수는 fold-structured 아님**. -/
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
