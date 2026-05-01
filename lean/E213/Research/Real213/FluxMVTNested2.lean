import E213.Research.Real213.FluxMVTNested

/-!
# Research.Real213FluxMVTNested2

Phase CJ: more nested midpoint MVT witnesses.

Math: f(x) = mid(mid(x, x²), x²) = (x + 3x²)/4.
- f(0) = 0, f(1) = 1, passthrough.
- f'(x) = (1 + 6x)/4. = 1 when 6x = 3 → x = 1/2 dyadic.
-/

namespace E213.Research.Real213.FluxMVTNested2

open E213.Firmware E213.Hypervisor

/-- ★ d/dx [mid(mid(x, x²), x²)] at x = 1/2 = 1. -/
theorem mid_mid_id_square_square_derivative_at_half :
    (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2)
      = constCut 1 1 := by
  show cutMid ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2))
              (squareIsDifferentiable.derivative (constCut 1 2))
       = constCut 1 1
  rw [mid_id_square_derivative_at_half, squareDerivative_at_half]
  exact cutMid_self_constCut 1 1 (by decide)

/-- HasDyadicMVTWitness for mid(mid(x, x²), x²). -/
def HasDyadicMVTWitness.mid_mid_id_square_square :
    HasDyadicMVTWitness (midIsDifferentiable
      (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
      squareIsDifferentiable) :=
  { witness := constCut 1 2
    proof := mid_mid_id_square_square_derivative_at_half }

/-- ★ Phase CJ: existential witness for mid(mid(x, x²), x²). -/
theorem mid_mid_id_square_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            squareIsDifferentiable).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists
    HasDyadicMVTWitness.mid_mid_id_square_square

/-- Phase CJ capstone. -/
theorem mid_mid_id_square_square_capstone :
    (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2)
        = constCut 1 1
    ∧ (∃ c, (midIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
              squareIsDifferentiable).derivative c = constCut 1 1) :=
  ⟨mid_mid_id_square_square_derivative_at_half,
   mid_mid_id_square_square_has_dyadic_witness⟩

end E213.Research.Real213.FluxMVTNested2
