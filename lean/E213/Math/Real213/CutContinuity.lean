import E213.Math.Max213
import E213.Math.Analysis.CauchyComplete

/-!
# Real213CutContinuity: continuity of cut-functions (1-D2)

Cut-level continuity of functions f : RealCut → RealCut.

## Definition

`isLocallyDetermined f` := the value of f at (m, k) depends only on
values of cx within a *bounded range*.

## Significance

213-native continuity = "f's value at (m, k) only depends on cx's
values at precisions ≤ N(m, k)".

This form is the cut-level counterpart of standard ε-δ continuity —
consistent with Bishop locatedness.
-/

namespace E213.Math.Real213.CutContinuity

open E213.Firmware E213.Hypervisor

/-- **CutFunction**: cut → cut transformer. -/
abbrev CutFunction := (Nat → Nat → Bool) → (Nat → Nat → Bool)

/-- **isLocallyDetermined**: the result of f at (m, k) depends only
    on values of cx within ≤ N. -/
def isLocallyDetermined (f : CutFunction) : Prop :=
  ∀ m k, ∃ N : Nat,
    ∀ cx cy : Nat → Nat → Bool,
      (∀ m' k', m' ≤ N → k' ≤ N → cx m' k' = cy m' k') →
      f cx m k = f cy m k

/-- **Identity is locally-determined**: just reads cx at (m, k). -/
theorem id_locallyDetermined : isLocallyDetermined id := by
  intro m k
  refine ⟨max m k, ?_⟩
  intro cx cy h
  exact h m k (E213.Math.Max213.le_max_left _ _) (E213.Math.Max213.le_max_right _ _)

open E213.Firmware E213.Hypervisor

/-- **Const cut function**: f cx = c (fixed). -/
def constCutFn (c : Nat → Nat → Bool) : CutFunction := fun _ => c

/-- **Const is locally-determined**: vacuously, depends on nothing. -/
theorem constCutFn_locallyDetermined (c : Nat → Nat → Bool) :
    isLocallyDetermined (constCutFn c) := by
  intro _ _
  exact ⟨0, fun _ _ _ => rfl⟩

end E213.Math.Real213.CutContinuity
