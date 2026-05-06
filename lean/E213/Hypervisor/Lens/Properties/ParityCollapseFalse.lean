import E213.Hypervisor.Lens.Instances.Parity

/-!
# ParityLensCollapseFalse: parityLens is Collapse-False

Explicit witness for the BoolSqClassification claim in PAPER1 §3.4:
parityLens.combine x x = false for all x.
-/

namespace E213.Hypervisor.Lens.Properties.ParityCollapseFalse

open E213.Hypervisor
open E213.Meta

/-- The self-combine of parityLens is always false (Collapse-False class). -/
theorem parityLens_collapse_false (x : Bool) :
    parityLens.combine x x = false := by
  cases x <;> rfl

end E213.Hypervisor.Lens.Properties.ParityCollapseFalse
