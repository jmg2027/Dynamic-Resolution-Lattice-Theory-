import E213.Lib.Math.Multivariable.MultiCut

/-!
# Multivariable — Partial derivative

`partialAt f i x` slices a multivariable function `f : MultiCut n → Cut`
to a single-variable function by varying only the i-th coordinate
while fixing the rest.

```
partialAt f i x : Cut → Cut := fun y => f (x.update i y)
```

This is the *single-variable function in disguise* — `IsDifferentiable`
applies to it directly.  No new derivative machinery needed.

213-native: differentiation over multiple variables = differentiation
of *each* slice via `IsDifferentiable` from `Lib/Math/Analysis/Differentiation/`.
-/

namespace E213.Lib.Math.Multivariable.PartialDerivative

open E213.Lib.Math.Multivariable.MultiCut (MultiCut update)

/-- Partial slice: `f` restricted to varying only the `i`-th coord. -/
def partialAt {n : Nat} (f : MultiCut n → (Nat → Nat → Bool))
    (i : Fin n) (x : MultiCut n) : (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  fun y => f (update x i y)

/-- Partial slice at fixed `i, x` is a `Cut → Cut` function (rfl). -/
theorem partialAt_signature {n : Nat} (f : MultiCut n → (Nat → Nat → Bool))
    (i : Fin n) (x : MultiCut n) :
    partialAt f i x = fun y => f (update x i y) := rfl

/-- Constant-valued multi-function has constant partial slice
    (rfl): a constant function has zero slice derivative in
    every coordinate. -/
theorem partialAt_const {n : Nat} (c : Nat → Nat → Bool)
    (i : Fin n) (x : MultiCut n) :
    partialAt (fun _ => c) i x = fun _ => c := rfl

/-- Projection to coordinate `i` (= the function `x ↦ xᵢ`). -/
def proj {n : Nat} (i : Fin n) : MultiCut n → (Nat → Nat → Bool) :=
  fun x => x i

/-- ★ **Partial derivative of projection** ★ — `partialAt (proj i) i x`
    at varying `y` returns `y` (the i-th coord becomes whatever
    we substitute).  This is the "∂xᵢ/∂xᵢ = 1" identity in 213-native:
    the slice is the identity function. -/
theorem partialAt_proj_self {n : Nat} (i : Fin n) (x : MultiCut n)
    (y : Nat → Nat → Bool) :
    partialAt (proj i) i x y = y := by
  show update x i y i = y
  exact E213.Lib.Math.Multivariable.MultiCut.update_self x i y

end E213.Lib.Math.Multivariable.PartialDerivative
