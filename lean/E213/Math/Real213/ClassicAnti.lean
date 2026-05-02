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
open E213.Math.Real213.ClassicCalc (ClassicCalc)
open E213.Math.Real213.ClassicCalc.ClassicCalc
  (id_calc square_calc cube_calc)
open E213.Math.Real213.Antiderivative (IsAntiderivative)
open E213.Math.Real213.AntiderivativeStructural.IsAntiderivative
  (fromDifferentiable)
open E213.Math.Real213.IntegralViaAnti.IsAntiderivative (integral)
open E213.Math.Real213.FluxFTC.FluxCut (ftc_id_unitBracket)
open E213.Math.Real213.FluxFTCPolynomial.FluxCut
  (fluxAlong_square_unitBracket fluxAlong_cube_unitBracket)

namespace ClassicCalc

/-- ★ ClassicCalc → IsAntiderivative (structural extraction). -/
def toAntiderivative {F} (cc : ClassicCalc F) :
    IsAntiderivative F cc.diff cc.diff.derivative :=
  fromDifferentiable cc.diff

/-- ★ Integral via ClassicCalc: F's flux along bracket. -/
def integralCC {F} (cc : ClassicCalc F) (db : DyadicBracket) : FluxCut :=
  integral (toAntiderivative cc) db

/-- ★ id_calc gives integral 1 over unit. -/
theorem integralCC_id_unit :
    integralCC id_calc unitBracket = ofCut (constCut 1 1) := by
  show fluxAlong id unitBracket = ofCut (constCut 1 1)
  exact ftc_id_unitBracket

/-- ★ square_calc gives integral 1 over unit (x² boundary 1²-0²=1). -/
theorem integralCC_square_unit :
    integralCC square_calc unitBracket = ofCut (constCut 1 1) := by
  show fluxAlong (fun x => cutMul x x) unitBracket
       = ofCut (constCut 1 1)
  exact fluxAlong_square_unitBracket

/-- Phase CR capstone: ClassicCalc gives integral via antiderivative. -/
theorem integralCC_capstone :
    integralCC id_calc unitBracket = ofCut (constCut 1 1)
    ∧ integralCC square_calc unitBracket = ofCut (constCut 1 1)
    ∧ integralCC cube_calc unitBracket = ofCut (constCut 1 1) :=
  ⟨integralCC_id_unit, integralCC_square_unit, by
    show fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket
         = ofCut (constCut 1 1)
    exact fluxAlong_cube_unitBracket⟩

end ClassicCalc

end E213.Math.Real213.ClassicAnti
