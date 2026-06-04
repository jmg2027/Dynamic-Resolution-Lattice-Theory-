import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Analysis.Integration.Antiderivative
import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Lib.Math.Analysis.ODE.NewtonSecond

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# IndefiniteIntegral
★ indefinite integral as a flux-valued function ★

For F antiderivative of f, the indefinite integral from 0 to x is
F(x) - F(0).  In flux form:
  indefIntFromZero hF x := { forward := F x, backward := F 0 }

This represents ∫_0^x f dt cohomologically.

  indefIntFromZero hF (constCut 1 1) = boundary at x = 1
  indefIntFromZero hF (constCut 0 1) = balanced (= 0)
-/

namespace E213.Lib.Math.Analysis.Integration.IndefiniteIntegral

open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Lib.Math.Analysis.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Lib.Math.Analysis.Integration.Antiderivative (IsAntiderivative)
open E213.Lib.Math.Analysis.Integration.Antiderivative.IsAntiderivative (id_anti)
open E213.Lib.Math.Analysis.AntiderivativeCombinators.IsAntiderivative (add_anti)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)

namespace IsAntiderivative

/-- ★ Indefinite integral from 0 to x via flux. -/
def indefIntFromZero {F sF f} (_hF : IsAntiderivative F sF f)
    (x : Nat → Nat → Bool) : FluxCut :=
  { forward := F x, backward := F (constCut 0 1) }

/-- ★ Indefinite integral at x = 1 of constant 1 (via id_anti) = 1. -/
theorem indefIntFromZero_one_at_one :
    indefIntFromZero id_anti (constCut 1 1) = FluxCut.ofCut (constCut 1 1) :=
  rfl

/-- ★ Indefinite integral at x = 0 is balanced (= 0). -/
theorem indefIntFromZero_at_zero {F sF f} (hF : IsAntiderivative F sF f) :
    (indefIntFromZero hF (constCut 0 1)).forward
      = (indefIntFromZero hF (constCut 0 1)).backward :=
  rfl

/-- ★ Indefinite integral linearity: ∫_0^x (f+g) = (∫_0^x f) + (∫_0^x g). -/
theorem indefIntFromZero_add {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g)
    (x : Nat → Nat → Bool) :
    indefIntFromZero (add_anti hF hG) x
      = { forward := cutSum (F x) (G x),
          backward := cutSum (F (constCut 0 1)) (G (constCut 0 1)) } :=
  rfl

end IsAntiderivative


end E213.Lib.Math.Analysis.Integration.IndefiniteIntegral
