import E213.Math.Real213.Antiderivative
import E213.Math.Real213.IntegralViaAnti

/-!
# Research.Real213ClassicAnti

Phase CR: ★ ClassicCalc → IsAntiderivative connection ★

Every ClassicCalc instance trivially yields an IsAntiderivative
of its computed derivative, plus the integral via flux.
-/

namespace E213.Math.Real213.ClassicAnti

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.ClassicCalc (ClassicCalc_at)
open E213.Math.Real213.Antiderivative (IsAntiderivative)
open E213.Math.Real213.AntiderivativeStructural.IsAntiderivative
  (fromDifferentiable)
open E213.Math.Real213.IntegralViaAnti.IsAntiderivative (integral)
open E213.Math.Real213.FluxFTCPolynomial.FluxCut
  (fluxAlong_square_unitBracket_forward_at
   fluxAlong_square_unitBracket_backward_at
   fluxAlong_cube_unitBracket_forward_at
   fluxAlong_cube_unitBracket_backward_at)

namespace ClassicCalc_at

open E213.Math.Real213.ClassicCalc.ClassicCalc_at
  (id_calc square_calc cube_calc)

/-- ★ ClassicCalc_at → IsAntiderivative (structural extraction). -/
def toAntiderivative {F} (cc : ClassicCalc_at F) :
    IsAntiderivative F cc.diff cc.diff.derivative :=
  fromDifferentiable cc.diff

/-- ★ Integral via ClassicCalc_at: F's flux along bracket. -/
def integralCC {F} (cc : ClassicCalc_at F) (db : DyadicBracket) : FluxCut :=
  integral (toAntiderivative cc) db

/-- ★ id_calc gives integral 1 over unit, forward (PURE pointwise). -/
theorem integralCC_id_unit_forward_at (m k : Nat) :
    (integralCC id_calc unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := rfl

/-- ★ id_calc gives integral 1 over unit, backward (PURE pointwise). -/
theorem integralCC_id_unit_backward_at (m k : Nat) :
    (integralCC id_calc unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := rfl

/-- ★ square_calc gives integral 1 over unit, forward (PURE pointwise). -/
theorem integralCC_square_unit_forward_at (m k : Nat) :
    (integralCC square_calc unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k :=
  fluxAlong_square_unitBracket_forward_at m k

/-- ★ square_calc gives integral 1 over unit, backward (PURE pointwise). -/
theorem integralCC_square_unit_backward_at (m k : Nat) :
    (integralCC square_calc unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k :=
  fluxAlong_square_unitBracket_backward_at m k

/-- ★ cube_calc gives integral 1 over unit, forward (PURE pointwise). -/
theorem integralCC_cube_unit_forward_at (m k : Nat) :
    (integralCC cube_calc unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k :=
  fluxAlong_cube_unitBracket_forward_at m k

/-- ★ cube_calc gives integral 1 over unit, backward (PURE pointwise). -/
theorem integralCC_cube_unit_backward_at (m k : Nat) :
    (integralCC cube_calc unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k :=
  fluxAlong_cube_unitBracket_backward_at m k

end ClassicCalc_at

end E213.Math.Real213.ClassicAnti
