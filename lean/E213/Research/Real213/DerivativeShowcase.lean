import E213.Research.Real213.FluxMVTPattern

/-!
# Research.Real213DerivativeShowcase

Phase CI: decide-checked derivative evaluations at multiple dyadic
points.  Demonstrates the framework's executable computation —
ML gradient descent ground truth.

  d/dx [x²] at x = 0    queried Boolean values
  d/dx [x²] at x = 1/4  queried Boolean values
  d/dx [x²] at x = 1/2  matches squareDerivative_at_half
  d/dx [x²] at x = 3/4  queried Boolean values
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- d/dx [x²] at x = 0 query at (m=0, k=0): true (slope = 0 ≤ 0). -/
example : squareIsDifferentiable.derivative (constCut 0 1) 0 0 = true := by decide

/-- d/dx [x²] at x = 0 query at (m=0, k=1): true (slope = 0 ≤ 0). -/
example : squareIsDifferentiable.derivative (constCut 0 1) 0 1 = true := by decide

/-- d/dx [x²] at x = 1/4 query at (m=0, k=0): true. -/
example : squareIsDifferentiable.derivative (constCut 1 4) 0 0 = true := by decide

/-- d/dx [x²] at x = 1/4 query at (m=1, k=0): true (slope ≤ 1). -/
example : squareIsDifferentiable.derivative (constCut 1 4) 1 0 = true := by decide

/-- d/dx [x²] at x = 1/2 query at (m=0, k=0): true. -/
example : squareIsDifferentiable.derivative (constCut 1 2) 0 0 = true := by decide

/-- d/dx [x²] at x = 1/2 query at (m=1, k=0): true (slope = 1). -/
example : squareIsDifferentiable.derivative (constCut 1 2) 1 0 = true := by decide

/-- d/dx [x²] at x = 3/4 query at (m=0, k=0): true. -/
example : squareIsDifferentiable.derivative (constCut 3 4) 0 0 = true := by decide

/-- d/dx [x²] at x = 1 (right endpoint) query at (m=0, k=0): true. -/
example : squareIsDifferentiable.derivative (constCut 1 1) 0 0 = true := by decide

/-- d/dx [x²] at x = 1 query at (m=2, k=0): true (slope = 2 ≤ 2). -/
example : squareIsDifferentiable.derivative (constCut 1 1) 2 0 = true := by decide

/-- d/dx [x³] at x = 0 query at (m=0, k=0): true. -/
example : cubeIsDifferentiable.derivative (constCut 0 1) 0 0 = true := by decide

/-- d/dx [x³] at x = 1/2 query at (m=0, k=0): true (slope = 3/4 ≤ ?). -/
example : cubeIsDifferentiable.derivative (constCut 1 2) 0 0 = true := by decide

/-- d/dx [id] at any point: always constCut 1 1 (rfl). -/
example (c : Nat → Nat → Bool) :
    idIsDifferentiable.derivative c = constCut 1 1 := rfl

/-- d/dx [const c] at any point: always constCut 0 1 (rfl). -/
example (c x : Nat → Nat → Bool) :
    (constIsDifferentiable c).derivative x = constCut 0 1 := rfl

end E213.Research.Real213.CutSum
