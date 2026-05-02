import E213.Math.Real213.ClassicCalcHigher
import E213.Math.Real213.DifferentiableHighOrder

/-!
# Research.Real213ClassicCalcExtreme

Phase BO: ClassicCalc to high polynomial degrees 9, 10, 12, 16.

Continues the pattern: every polynomial chain has matching
IsDifferentiable + Passthrough → ClassicCalc.
-/

namespace E213.Math.Real213.ClassicCalcExtreme

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)

namespace ClassicCalc

/-- x⁹ ∈ ClassicCalc (quartic · quintic). -/
def nonic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  { diff := nonicIsDifferentiable
    pass := FluxCut.Passthrough.mul_pass
              FluxCut.Passthrough.quartic_pass
              FluxCut.Passthrough.quintic_pass }

/-- x¹⁰ ∈ ClassicCalc (quintic · quintic). -/
def decic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x)
        (cutMul x (cutMul x x))) (cutMul (cutMul x x)
        (cutMul x (cutMul x x)))) :=
  { diff := decicIsDifferentiable
    pass := FluxCut.Passthrough.mul_pass
              FluxCut.Passthrough.quintic_pass
              FluxCut.Passthrough.quintic_pass }

/-- x¹² ∈ ClassicCalc (quartic · octic). -/
def dodecic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul (cutMul x x) (cutMul x x))
                (cutMul (cutMul x x) (cutMul x x)))) :=
  { diff := dodecicIsDifferentiable
    pass := FluxCut.Passthrough.mul_pass
              FluxCut.Passthrough.quartic_pass
              (FluxCut.Passthrough.mul_pass
                FluxCut.Passthrough.quartic_pass
                FluxCut.Passthrough.quartic_pass) }

/-- x¹⁶ ∈ ClassicCalc (octic · octic via mul_pass). -/
def hexadecic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x x)))
        (cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x x)))) :=
  { diff := hexadecicIsDifferentiable
    pass := FluxCut.Passthrough.mul_pass
              (FluxCut.Passthrough.mul_pass
                FluxCut.Passthrough.quartic_pass
                FluxCut.Passthrough.quartic_pass)
              (FluxCut.Passthrough.mul_pass
                FluxCut.Passthrough.quartic_pass
                FluxCut.Passthrough.quartic_pass) }

end ClassicCalc

end E213.Math.Real213.ClassicCalcExtreme
