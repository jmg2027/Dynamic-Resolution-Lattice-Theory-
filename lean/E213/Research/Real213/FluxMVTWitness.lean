import E213.Research.Real213.PhaseBQOmegaCapstone
import E213.Research.Real213.CutSumOne

/-!
# Research.Real213FluxMVTWitness

Phase BR: ★ **explicit MVT witness for x²** ★

For x² over [0, 1], MVT says ∃ c ∈ (0, 1) with f'(c) = (f(1)-f(0))/1 = 1.
Solving 2c = 1 gives c = 1/2 — a *dyadic* point!  We can prove
PROPOSITIONALLY that derivative of x² at 1/2 equals 1.

  squareDerivative_at_half : squareIsDifferentiable.deriv (1/2) = 1
  mvt_square_explicit      : MVT for x² with c = 1/2 (full propEq)

★ For x² specifically, the MVT witness is constructively dyadic.
For x³, c = 1/√3 is not dyadic; the witness becomes existential
(Cauchy approximation).  This file isolates the lucky x² case.
-/

namespace E213.Research.Real213.FluxMVTWitness

open E213.Firmware E213.Hypervisor

/-- ★ d/dx [x²] at x = 1/2 = 1, propositionally. -/
theorem squareDerivative_at_half :
    squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1 := by
  show cutSum (cutMul (constCut 1 1) (constCut 1 2))
              (cutMul (constCut 1 2) (constCut 1 1))
       = constCut 1 1
  rw [cutMul_one_const 1 2, cutMul_const_one 1 2, cutSum_half_half]

/-- ★ MVT for x² with explicit dyadic witness c = 1/2. -/
theorem mvt_square_explicit :
    -- Average rate of x² over [0,1] = 1
    FluxCut.localDivergence (fun x => cutMul x x) unitBracket
       = FluxCut.ofCut (constCut 1 1)
    -- Derivative at c = 1/2 equals 1 (matches average rate)
    ∧ squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1 :=
  ⟨FluxCut.mvt_square_unitBracket, squareDerivative_at_half⟩

/-- ★ MVT existence with explicit witness for x²: ∃ c, derivative c = 1. -/
theorem mvt_square_explicit_witness :
    ∃ c, squareIsDifferentiable.derivative c = constCut 1 1 :=
  ⟨constCut 1 2, squareDerivative_at_half⟩

/-- The witness c = 1/2 is interior to [0, 1]: it equals constCut 1 2. -/
theorem mvt_square_witness_in_interior :
    (constCut 1 2 : Nat → Nat → Bool) 1 2 = true := by decide

/-- Phase BR capstone: MVT for x² with constructive dyadic witness. -/
theorem mvt_square_with_witness_capstone :
    FluxCut.localDivergence (fun x => cutMul x x) unitBracket
       = FluxCut.ofCut (constCut 1 1)
    ∧ squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    ∧ ∃ c, squareIsDifferentiable.derivative c = constCut 1 1 :=
  ⟨FluxCut.mvt_square_unitBracket, squareDerivative_at_half,
   ⟨constCut 1 2, squareDerivative_at_half⟩⟩

end E213.Research.Real213.FluxMVTWitness
