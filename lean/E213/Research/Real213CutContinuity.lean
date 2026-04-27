import E213.Research.Real213CauchyComplete

/-!
# Research.Real213CutContinuity: continuity of cut-functions (Phase D1-D2)

Cut-level continuity of functions f : RealCut → RealCut.

## 정의

`isLocallyDetermined f` := f 의 value at (m, k) 가 cx 의 *bounded
range* 의 values 에 만 의존.

## 의의

213-native continuity = "f's value at (m, k) only depends on cx's
values at precisions ≤ N(m, k)".

이 form 은 standard ε-δ continuity 의 cut counterpart — Bishop
locatedness 와 정 합.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **CutFunction**: cut → cut transformer. -/
abbrev CutFunction := (Nat → Nat → Bool) → (Nat → Nat → Bool)

/-- **isLocallyDetermined**: f 의 (m, k) 결과 가 cx 의 ≤ N 안 values 만
    의존. -/
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
  exact h m k (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end E213.Research.Real213CutSum

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **Const cut function**: f cx = c (fixed). -/
def constCutFn (c : Nat → Nat → Bool) : CutFunction := fun _ => c

/-- **Const is locally-determined**: vacuously, depends on nothing. -/
theorem constCutFn_locallyDetermined (c : Nat → Nat → Bool) :
    isLocallyDetermined (constCutFn c) := by
  intro _ _
  exact ⟨0, fun _ _ _ => rfl⟩

end E213.Research.Real213CutSum
