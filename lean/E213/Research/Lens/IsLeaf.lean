import E213.Hypervisor.Lens
import E213.Research.Lens.Identity

/-!
# Research.IsLeafLens: "leaf indicator" as a valid Lens Bool

A natural entry in the Lens catalogue of PAPER1 §3.4:
view r = true iff r is a leaf (Raw.a or Raw.b).

## Core

`isLeafLens` = ⟨true, true, λ _ _. false⟩.  base values = true
(leaves), combine = const false (result of slash is not a leaf).

Raw is a leaf iff view = true (decidable).

BoolSqClassification: since combine x x = false, this is Collapse-False.
-/

namespace E213.Research.IsLeafLens

open E213.Firmware E213.Hypervisor

/-- Leaf-indicator Lens. -/
def isLeafLens : Lens Bool := ⟨true, true, fun _ _ => false⟩

theorem isLeafLens_a : isLeafLens.view Raw.a = true := rfl
theorem isLeafLens_b : isLeafLens.view Raw.b = true := rfl

theorem isLeafLens_combine_sym :
    ∀ u v, isLeafLens.combine u v = isLeafLens.combine v u := by
  intros _ _; rfl

end E213.Research.IsLeafLens
