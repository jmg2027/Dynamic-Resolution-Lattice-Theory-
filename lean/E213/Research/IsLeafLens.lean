import E213.Hypervisor.Lens
import E213.Research.IdentityLens

/-!
# Research.IsLeafLens: "leaf indicator" 가 valid Lens Bool

PAPER1 §3.4 의 Lens catalogue 의 자연 한 entry:
view r = true iff r is a leaf (Raw.a 또 는 Raw.b).

## 핵심

`isLeafLens` = ⟨true, true, λ _ _. false⟩.  base values = true
(leaves), combine = const false (slash 의 결과 는 leaf 아님).

Raw 가 leaf iff view = true (decidable).

BoolSqClassification: combine x x = false 이므로 Collapse-False.
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
