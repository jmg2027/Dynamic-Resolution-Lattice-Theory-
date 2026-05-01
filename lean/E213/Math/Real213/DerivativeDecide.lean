import E213.Math.Real213.PhaseANOmegaCapstone

/-!
# Research.Real213DerivativeDecide

Phase AO: concrete decide-checked derivative evaluations at dyadic
points.  Validates that the IsDifferentiable framework produces
*computable* derivatives — feeding the user-vision "dyadic ML
gradient descent" application directly.

Each test queries `f.derivative x m k` and verifies via `by decide`
that the structural derivative reduces to expected Boolean values.

## Tests

  d/dx [x] = constCut 1 1 (rfl-clean at any point)
  d/dx [c] = constCut 0 1 (rfl-clean at any point)
  d/dx [x²] = structural (1·x + x·1) — decide-checked Booleans
  d/dx [x³] structural — decide-checked at simple points
-/

namespace E213.Math.Real213.DerivativeDecide

open E213.Firmware E213.Hypervisor

/-- d/dx [x] at any point evaluates to constCut 1 1 (rfl). -/
example (x : Nat → Nat → Bool) (m k : Nat) :
    idIsDifferentiable.derivative x m k = (constCut 1 1) m k := rfl

/-- d/dx [c] at any point evaluates to constCut 0 1 (rfl). -/
example (c x : Nat → Nat → Bool) (m k : Nat) :
    (constIsDifferentiable c).derivative x m k = (constCut 0 1) m k := rfl

/-- constCut 1 1 at (2, 0): 0+1 ≤ 2 = true.  Identity slope = 1. -/
example : (constCut 1 1 : Nat → Nat → Bool) 2 0 = true := by decide

/-- d/dx [x] queried at (m=2, k=0) — true. -/
example : idIsDifferentiable.derivative (constCut 7 13) 2 0 = true := by decide

/-- d/dx [x²] at x=0 queried at (m=0, k=0) — slope 0, threshold true. -/
example : squareIsDifferentiable.derivative (constCut 0 1) 0 0 = true := by decide

/-- d/dx [x²] at x=0 queried at (m=1, k=0) — slope 0, threshold true. -/
example : squareIsDifferentiable.derivative (constCut 0 1) 1 0 = true := by decide

/-- d/dx [x²] at x=1/2 queried at (m=0, k=0). -/
example : squareIsDifferentiable.derivative (constCut 1 2) 0 0 = true := by decide

/-- d/dx [x³] at x=0 queried at (m=0, k=0). -/
example : cubeIsDifferentiable.derivative (constCut 0 1) 0 0 = true := by decide

/-- Concrete bool-equality: identity derivative ≡ const-1 derivative pointwise. -/
example (x : Nat → Nat → Bool) :
    idIsDifferentiable.derivative x = constCutFn (constCut 1 1) x := rfl

/-- Distinctness at concrete x: id derivative ≠ const-0 derivative
    at the (m=0, k=1) bool query.  At this point constCut 1 1 = false
    while constCut 0 1 = true — distinguishable. -/
example :
    idIsDifferentiable.derivative (constCut 5 7) 0 1
      ≠ (constIsDifferentiable (constCut 0 1)).derivative (constCut 5 7) 0 1 := by decide

end E213.Math.Real213.DerivativeDecide
