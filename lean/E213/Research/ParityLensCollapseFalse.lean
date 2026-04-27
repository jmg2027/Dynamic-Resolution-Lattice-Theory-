import E213.Meta.ParityLens

/-!
# Research.ParityLensCollapseFalse: parityLens 가 Collapse-False

PAPER1 §3.4 의 BoolSqClassification 분류 claim 의 explicit
witness: parityLens.combine x x = false 모든 x.
-/

namespace E213.Research.ParityLensCollapseFalse

open E213.Hypervisor
open E213.Meta

/-- The self-combine of parityLens is always false (Collapse-False class). -/
theorem parityLens_collapse_false (x : Bool) :
    parityLens.combine x x = false := by
  cases x <;> rfl

end E213.Research.ParityLensCollapseFalse
