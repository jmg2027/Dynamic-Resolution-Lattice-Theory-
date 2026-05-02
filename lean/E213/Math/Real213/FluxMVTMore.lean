import E213.Math.Real213.HasDyadicMVTWitness

/-!
# Research.Real213FluxMVTMore

Phase BU: more dyadic MVT witnesses.  Shows that the dyadic-witness
class is non-trivially populated beyond x².

  mid(x, x²) at c = 1/2 : derivative = 1 (propEq)
  HasDyadicMVTWitness.mid_id_square : new instance

Mathematical observation: f(x) = (x + x²)/2 has derivative (1+2x)/2,
which equals 1 when x = 1/2.  Witness c = 1/2 dyadic.
-/

namespace E213.Math.Real213.FluxMVTMore

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★ d/dx [(x + x²)/2] at x = 1/2 = 1, propositionally. -/
theorem mid_id_square_derivative_at_half :
    (midIsDifferentiable idIsDifferentiable squareIsDifferentiable).derivative
        (constCut 1 2) = constCut 1 1 := by
  show cutMid (constCut 1 1)
              (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                      (cutMul (constCut 1 2) (constCut 1 1)))
       = constCut 1 1
  rw [cutMul_one_const 1 2, cutMul_const_one 1 2, cutSum_half_half]
  exact cutMid_self_constCut 1 1 (by decide)

/-- HasDyadicMVTWitness instance for mid(x, x²). -/
def HasDyadicMVTWitness.mid_id_square :
    HasDyadicMVTWitness (midIsDifferentiable idIsDifferentiable
                          squareIsDifferentiable) :=
  { witness := constCut 1 2
    proof := mid_id_square_derivative_at_half }

/-- mid(x, x²) has constructive MVT existence. -/
theorem mid_id_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
            ).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.mid_id_square

/-- Phase BU capstone: 2 functions with constructive dyadic MVT witnesses. -/
theorem mvt_witness_extended_capstone :
    -- (1) x² witness c = 1/2
    squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    -- (2) mid(x, x²) witness c = 1/2
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) = constCut 1 1
    -- (3) Both yield existential MVT
    ∧ (∃ c, squareIsDifferentiable.derivative c = constCut 1 1)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative c = constCut 1 1) :=
  ⟨squareDerivative_at_half,
   mid_id_square_derivative_at_half,
   square_has_dyadic_witness,
   mid_id_square_has_dyadic_witness⟩

end E213.Math.Real213.FluxMVTMore
