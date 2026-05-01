import E213.Math.Real213.ClassicCalc
import E213.Math.Real213.DifferentiableHigherPow

/-!
# Research.Real213ClassicCalcHigher

Phase BM: ClassicCalc to polynomial chain degrees 4-8.
Each gets explicit derivative + Passthrough + one-liner MVT/FTC.
-/

namespace E213.Math.Real213.ClassicCalcHigher

open E213.Firmware E213.Hypervisor

namespace ClassicCalc

/-- x⁴ ∈ ClassicCalc. -/
def quartic_calc :
    ClassicCalc (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  { diff := quarticIsDifferentiable
    pass := FluxCut.Passthrough.quartic_pass }

/-- x⁵ ∈ ClassicCalc. -/
def quintic_calc :
    ClassicCalc (fun x => cutMul (cutMul x x)
                                  (cutMul x (cutMul x x))) :=
  { diff := quinticIsDifferentiable
    pass := FluxCut.Passthrough.quintic_pass }

/-- x⁶ ∈ ClassicCalc (cube · cube). -/
def sextic_calc :
    ClassicCalc (fun x => cutMul (cutMul x (cutMul x x))
                                  (cutMul x (cutMul x x))) :=
  { diff := sexticIsDifferentiable
    pass := FluxCut.Passthrough.mul_pass
              FluxCut.Passthrough.cube_pass
              FluxCut.Passthrough.cube_pass }

/-- x⁷ ∈ ClassicCalc (cube · quartic). -/
def septic_calc :
    ClassicCalc (fun x => cutMul (cutMul x (cutMul x x))
                                  (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := septicIsDifferentiable
    pass := FluxCut.Passthrough.mul_pass
              FluxCut.Passthrough.cube_pass
              FluxCut.Passthrough.quartic_pass }

/-- x⁸ ∈ ClassicCalc (quartic · quartic). -/
def octic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                  (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := octicIsDifferentiable
    pass := FluxCut.Passthrough.mul_pass
              FluxCut.Passthrough.quartic_pass
              FluxCut.Passthrough.quartic_pass }

/-- Phase BM capstone: 4-8 polynomial chain in ClassicCalc. -/
theorem classic_calc_higher_capstone :
    FluxCut.localDivergence
        (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
        = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence
        (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) unitBracket
        = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence
        (fun x => cutMul (cutMul x (cutMul x x))
                         (cutMul x (cutMul x x))) unitBracket
        = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence
        (fun x => cutMul (cutMul x (cutMul x x))
                         (cutMul (cutMul x x) (cutMul x x))) unitBracket
        = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence
        (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                         (cutMul (cutMul x x) (cutMul x x))) unitBracket
        = FluxCut.ofCut (constCut 1 1) :=
  ⟨quartic_calc.mvt, quintic_calc.mvt, sextic_calc.mvt,
   septic_calc.mvt, octic_calc.mvt⟩

end ClassicCalc

end E213.Math.Real213.ClassicCalcHigher
