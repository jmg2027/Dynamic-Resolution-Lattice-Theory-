import E213.Research.Real213CutContinuity

/-!
# Research.Real213CutFnData: data-bearing local determinedness

`isLocallyDetermined` 의 *data* form — Bishop modulus 의 cut function
counterpart.  Existence-only form 은 composition 시 Classical.choose
요구.  Data form 은 axiom-free composition.

## 정의

```
structure LocallyDeterminedData (f : CutFunction) where
  N : Nat → Nat → Nat
  prop : f's value at (m, k) determined by cx at ≤ N m k.
```
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **LocallyDeterminedData**: explicit modulus carried as data. -/
structure LocallyDeterminedData (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  N : Nat → Nat → Nat
  prop : ∀ m k, ∀ cx cy : Nat → Nat → Bool,
    (∀ m' k', m' ≤ N m k → k' ≤ N m k → cx m' k' = cy m' k') →
    f cx m k = f cy m k

/-- Identity 의 LocallyDeterminedData. -/
def idLDD : LocallyDeterminedData id where
  N := fun m k => max m k
  prop := by
    intro m k cx cy h
    exact h m k (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- Const 의 LocallyDeterminedData. -/
def constLDD (c : Nat → Nat → Bool) : LocallyDeterminedData (constCutFn c) where
  N := fun _ _ => 0
  prop := fun _ _ _ _ _ => rfl

end E213.Research.Real213CutSum

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- Max over (i, j) ∈ [0, M] × [0, K]. -/
def maxRange (f : Nat → Nat → Nat) (M K : Nat) : Nat :=
  match M with
  | 0 => maxRangeRow f 0 K
  | M+1 => max (maxRangeRow f (M+1) K) (maxRange f M K)
where
  maxRangeRow (f : Nat → Nat → Nat) (i : Nat) : Nat → Nat
    | 0 => f i 0
    | k+1 => max (f i (k+1)) (maxRangeRow f i k)

end E213.Research.Real213CutSum
