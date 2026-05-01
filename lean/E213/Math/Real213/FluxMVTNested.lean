import E213.Math.Real213.ClassicCalcCombinators
import E213.Math.Real213.HasDyadicMVTWitness

/-!
# Research.Real213FluxMVTNested

Phase CF: nested midpoint MVT witness chain.

Math: f(x) = (3x + x²)/4 = mid(x, mid(x, x²)).
- f(0) = 0, f(1) = 1, passthrough.
- f'(x) = (3 + 2x)/4. = 1 when 2x = 1 → x = 1/2 dyadic.

Witness c = 1/2 propagates through nested mid combinators.
-/

namespace E213.Math.Real213.FluxMVTNested

open E213.Firmware E213.Hypervisor

/-- ★ d/dx [mid(x, mid(x, x²))] at x = 1/2 = 1 propEq. -/
theorem mid_id_mid_id_square_derivative_at_half :
    (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) = constCut 1 1 := by
  show cutMid (idIsDifferentiable.derivative (constCut 1 2))
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) = constCut 1 1
  show cutMid (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) = constCut 1 1
  rw [mid_id_square_derivative_at_half]
  exact cutMid_self_constCut 1 1 (by decide)

/-- HasDyadicMVTWitness instance for mid(id, mid(id, x²)). -/
def HasDyadicMVTWitness.mid_id_mid_id_square :
    HasDyadicMVTWitness (midIsDifferentiable idIsDifferentiable
      (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)) :=
  { witness := constCut 1 2
    proof := mid_id_mid_id_square_derivative_at_half }

/-- mid(id, mid(id, x²)) has constructive MVT existence. -/
theorem mid_id_mid_id_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable idIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              )).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.mid_id_mid_id_square

/-- Phase CF capstone: nested mid witness chain. -/
theorem nested_mid_witness_capstone :
    -- (1) explicit witness
    (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) = constCut 1 1
    -- (2) MVT existence (constructive)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                )).derivative c = constCut 1 1) :=
  ⟨mid_id_mid_id_square_derivative_at_half,
   mid_id_mid_id_square_has_dyadic_witness⟩

end E213.Math.Real213.FluxMVTNested
