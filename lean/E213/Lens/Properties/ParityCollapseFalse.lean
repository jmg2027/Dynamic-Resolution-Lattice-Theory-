import E213.Lens.Instances.Parity

/-!
# ParityLensCollapseFalse: parityLens is Collapse-False

Explicit witness for the BoolSqClassification claim in PAPER1 §3.4:
parityLens.combine x x = false for all x.
-/

namespace E213.Lens.Properties.ParityCollapseFalse

open E213.Lens
open E213.Meta

/-- The self-combine of parityLens is always false (Collapse-False class). -/
theorem parityLens_collapse_false (x : Bool) :
    parityLens.combine x x = false := by
  cases x <;> rfl

end E213.Lens.Properties.ParityCollapseFalse
