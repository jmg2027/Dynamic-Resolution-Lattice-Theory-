import E213.Math.Analysis.Integration.Antiderivative
import E213.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Math.Analysis.Integration.IntegralViaAnti

import E213.Math.Real213.Core
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutSum
import E213.Math.Real213.Dyadic
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.Differentiation.Differentiable
/-!
# IntegralProperties
★ properties of the integral ★

Standard integration laws expressed in 213-native form:

  ∫(f+g)       = ∫f + ∫g       (linearity via add_anti)
  ∫_a^a f       = 0             (zero-length bracket)
  ∫(mid f g)   = mid (∫f) (∫g)  (midpoint linearity)

These follow structurally from the antiderivative class combinators.
-/

namespace E213.Math.Analysis.Integration.IntegralProperties

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.Dyadic (dyadicCut)
open E213.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Math.Analysis.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Math.Analysis.Integration.Antiderivative
  (IsAntiderivative)
open E213.Math.Analysis.Integration.Antiderivative.IsAntiderivative
  (id_anti)
open E213.Math.Analysis.AntiderivativeCombinators.IsAntiderivative
  (add_anti mid_anti)
open E213.Math.Analysis.Integration.IntegralViaAnti.IsAntiderivative (integral)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)

namespace IsAntiderivative

/-- ★ Integral additivity: ∫(f+g) over db = ∫f + ∫g. -/
theorem integral_add {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g)
    (db : DyadicBracket) :
    integral (add_anti hF hG) db
      = { forward := cutSum (F db.rightCut) (G db.rightCut),
          backward := cutSum (F db.leftCut) (G db.leftCut) } := rfl

/-- ★ Integral midpoint: ∫(mid f g) = mid (∫f) (∫g). -/
theorem integral_mid {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g)
    (db : DyadicBracket) :
    integral (mid_anti hF hG) db
      = { forward := cutMid (F db.rightCut) (G db.rightCut),
          backward := cutMid (F db.leftCut) (G db.leftCut) } := rfl

/-- ★ Zero-length bracket integral is balanced. -/
theorem integral_zero_length {F sF f}
    (hF : IsAntiderivative F sF f) (db : DyadicBracket)
    (h : db.numA = db.numB) :
    (integral hF db).forward = (integral hF db).backward := by
  show F db.rightCut = F db.leftCut
  show F (dyadicCut db.numB db.expE) = F (dyadicCut db.numA db.expE)
  rw [h]

end IsAntiderivative

/-- capstone: integration linearity properties. -/
theorem integral_properties_capstone (db : DyadicBracket) :
    -- (1) Additivity (rfl form via add_anti)
    integral (add_anti id_anti id_anti) db
      = ({ forward := cutSum (db.rightCut) (db.rightCut),
           backward := cutSum (db.leftCut) (db.leftCut) }
              : E213.Math.Analysis.FluxMVT.FluxCut.FluxCut)
    -- (2) Midpoint (rfl form via mid_anti)
    ∧ integral (mid_anti id_anti id_anti) db
      = ({ forward := cutMid (db.rightCut) (db.rightCut),
           backward := cutMid (db.leftCut) (db.leftCut) }
              : E213.Math.Analysis.FluxMVT.FluxCut.FluxCut) :=
  ⟨rfl, rfl⟩

end E213.Math.Analysis.Integration.IntegralProperties
