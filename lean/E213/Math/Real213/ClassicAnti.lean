import E213.Math.Real213.IntegralViaAnti

/-!
# Research.Real213ClassicAnti

Phase CR: ★ ClassicCalc → IsAntiderivative connection ★

Every ClassicCalc instance trivially yields an IsAntiderivative
of its computed derivative, plus the integral via flux.
-/

namespace E213.Math.Real213.ClassicAnti

open E213.Firmware E213.Hypervisor

namespace ClassicCalc

/-- ★ ClassicCalc → IsAntiderivative (structural extraction). -/
def toAntiderivative {F} (cc : ClassicCalc F) :
    IsAntiderivative F cc.diff cc.diff.derivative :=
  IsAntiderivative.fromDifferentiable cc.diff

/-- ★ Integral via ClassicCalc: F's flux along bracket. -/
def integralCC {F} (cc : ClassicCalc F) (db : DyadicBracket) : FluxCut :=
  IsAntiderivative.integral cc.toAntiderivative db

/-- ★ id_calc gives integral 1 over unit. -/
theorem integralCC_id_unit :
    integralCC id_calc unitBracket = FluxCut.ofCut (constCut 1 1) :=
  FluxCut.fluxAlong_id_unitBracket

/-- ★ square_calc gives integral 1 over unit (x² boundary 1²-0²=1). -/
theorem integralCC_square_unit :
    integralCC square_calc unitBracket = FluxCut.ofCut (constCut 1 1) :=
  FluxCut.fluxAlong_square_unitBracket

/-- Phase CR capstone: ClassicCalc gives integral via antiderivative. -/
theorem integralCC_capstone :
    integralCC id_calc unitBracket = FluxCut.ofCut (constCut 1 1)
    ∧ integralCC square_calc unitBracket = FluxCut.ofCut (constCut 1 1)
    ∧ integralCC cube_calc unitBracket = FluxCut.ofCut (constCut 1 1) :=
  ⟨integralCC_id_unit, integralCC_square_unit, by
    show FluxCut.fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket
         = FluxCut.ofCut (constCut 1 1)
    exact FluxCut.fluxAlong_cube_unitBracket⟩

end ClassicCalc

end E213.Math.Real213.ClassicAnti
