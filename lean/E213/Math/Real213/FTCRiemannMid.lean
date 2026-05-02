import E213.Math.Real213.FTCRiemannSquare
import E213.Math.Real213.ClassicCalcMid

/-!
# Research.Real213FTCRiemannMid

Phase CB: FTC-Riemann for mid(x, x²) at unit, depth 0.

Same propEq pattern as x² extends to mid(x, x²) since both
have MVT witness c = 1/2 = unitBracket midpoint.
-/

namespace E213.Math.Real213.FTCRiemannMid

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half)
open E213.Math.Real213.FTCRiemannSquare (unitBracket_midCut)
open E213.Math.Real213.CutMulOne (cutMul_one_one)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero cutMid_zero_zero)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut)

/-- ★ Riemann sum of mid(x, x²)'s derivative at unitBracket depth 0 = 1. -/
theorem riemann_mid_id_square_derivative_zero :
    riemannSampleSum (midIsDifferentiable idIsDifferentiable
                       squareIsDifferentiable).derivative unitBracket 0
      = constCut 1 1 := by
  show (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
          ).derivative unitBracket.midCut = constCut 1 1
  rw [unitBracket_midCut]
  exact mid_id_square_derivative_at_half

/-- fluxAlong mid(x, x²) at unitBracket = ofCut 1 (propEq). -/
theorem fluxAlong_mid_id_square_unit :
    fluxAlong (fun x => cutMid x (cutMul x x)) unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMid (constCut 1 1)
                            (cutMul (constCut 1 1) (constCut 1 1)),
          backward := cutMid (constCut 0 1)
                             (cutMul (constCut 0 1) (constCut 0 1)) }
                  : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero, cutMid_zero_zero]
  show ({ forward := cutMid (constCut 1 1) (constCut 1 1),
          backward := constCut 0 1 } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMid_self_constCut 1 1 (by decide)]

/-- ★ FTC-Riemann for mid(x, x²): depth 0 = boundary forward. -/
theorem ftc_riemann_mid_id_square_zero :
    riemannSampleSum (midIsDifferentiable idIsDifferentiable
                       squareIsDifferentiable).derivative unitBracket 0
      = (fluxAlong (fun x => cutMid x (cutMul x x))
          unitBracket).forward := by
  rw [riemann_mid_id_square_derivative_zero, fluxAlong_mid_id_square_unit]
  rfl

/-- Phase CB capstone: FTC-Riemann for mid(x, x²). -/
theorem ftc_riemann_mid_capstone :
    riemannSampleSum (midIsDifferentiable idIsDifferentiable
                       squareIsDifferentiable).derivative unitBracket 0
        = constCut 1 1
    ∧ fluxAlong (fun x => cutMid x (cutMul x x)) unitBracket
        = ofCut (constCut 1 1)
    ∧ riemannSampleSum (midIsDifferentiable idIsDifferentiable
                         squareIsDifferentiable).derivative unitBracket 0
        = (fluxAlong (fun x => cutMid x (cutMul x x))
            unitBracket).forward :=
  ⟨riemann_mid_id_square_derivative_zero,
   fluxAlong_mid_id_square_unit,
   ftc_riemann_mid_id_square_zero⟩

end E213.Math.Real213.FTCRiemannMid
