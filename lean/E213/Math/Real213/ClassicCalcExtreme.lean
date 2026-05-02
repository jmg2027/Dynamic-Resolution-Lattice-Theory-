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
open E213.Math.Real213.ClassicCalc (ClassicCalc)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough
  (mul_pass)
open E213.Math.Real213.FluxPassthroughCatalog.FluxCut.Passthrough
  (quartic_pass quintic_pass)
open E213.Math.Real213.DifferentiableHighOrder
  (nonicIsDifferentiable decicIsDifferentiable
   dodecicIsDifferentiable hexadecicIsDifferentiable)

namespace ClassicCalc

/-- x⁹ ∈ ClassicCalc (quartic · quintic). -/
def nonic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  { diff := nonicIsDifferentiable
    pass := mul_pass
              quartic_pass
              quintic_pass }

/-- x¹⁰ ∈ ClassicCalc (quintic · quintic). -/
def decic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x)
        (cutMul x (cutMul x x))) (cutMul (cutMul x x)
        (cutMul x (cutMul x x)))) :=
  { diff := decicIsDifferentiable
    pass := mul_pass
              quintic_pass
              quintic_pass }

/-- x¹² ∈ ClassicCalc (quartic · octic). -/
def dodecic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul (cutMul x x) (cutMul x x))
                (cutMul (cutMul x x) (cutMul x x)))) :=
  { diff := dodecicIsDifferentiable
    pass := mul_pass
              quartic_pass
              (mul_pass
                quartic_pass
                quartic_pass) }

/-- x¹⁶ ∈ ClassicCalc (octic · octic via mul_pass). -/
def hexadecic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x x)))
        (cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x x)))) :=
  { diff := hexadecicIsDifferentiable
    pass := mul_pass
              (mul_pass
                quartic_pass
                quartic_pass)
              (mul_pass
                quartic_pass
                quartic_pass) }

end ClassicCalc

end E213.Math.Real213.ClassicCalcExtreme
