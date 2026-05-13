import E213.Lib.Math.Analysis.Integration.Antiderivative

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Lib.Math.Analysis.FluxMVT.FluxCochain
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Analysis.FluxMVT.FluxFTC
/-!
# IntegralViaAnti
★ integration via antiderivative ★

Defines `integralViaAntiderivative`: given an IsAntiderivative
hypothesis, the "definite integral" of f over a bracket is the
flux of F along that bracket.

  ∫_a^b f dx = F(b) - F(a)  (cohomologically: fluxAlong F db)

This is the FTC at the symbolic level — integration becomes flux
of the antiderivative.
-/

namespace E213.Lib.Math.Analysis.Integration.IntegralViaAnti

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Analysis.FluxMVT.FluxCochain.FluxCut
  (fluxAlong isBalanced fluxAlong_const_isBalanced)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Lib.Math.Analysis.Integration.Antiderivative (IsAntiderivative)
open E213.Lib.Math.Analysis.Integration.Antiderivative.IsAntiderivative (id_anti const_anti)
open E213.Lib.Math.Analysis.FluxMVT.FluxFTC.FluxCut (fluxAlong_id_unitBracket)

namespace IsAntiderivative

/-- ★ Definite integral via antiderivative: F's flux along the bracket. -/
def integral {F sF f} (_hF : IsAntiderivative F sF f)
    (db : DyadicBracket) : FluxCut :=
  fluxAlong F db

/-- ★ FTC at symbolic level: integral hF db = fluxAlong F db (def). -/
theorem integral_eq_flux {F sF f} (hF : IsAntiderivative F sF f)
    (db : DyadicBracket) :
    integral hF db = fluxAlong F db := rfl

/-- ★ Integral of constant 1 over unit (via id antideriv) = 1 cohomologically. -/
theorem integral_one_unit :
    integral id_anti unitBracket = ofCut (constCut 1 1) :=
  fluxAlong_id_unitBracket

/-- ★ Integral of constant 0 over unit (via constant antideriv) is balanced. -/
theorem integral_zero_unit_balanced :
    isBalanced (integral (const_anti (constCut 0 1)) unitBracket) :=
  fluxAlong_const_isBalanced (constCut 0 1) unitBracket

end IsAntiderivative

/-- capstone: integration via antiderivative. -/
theorem integral_via_anti_capstone :
    -- (1) Integral of 1 over unit = 1 (in ofCut form)
    IsAntiderivative.integral IsAntiderivative.id_anti unitBracket
        = ofCut (constCut 1 1)
    -- (2) Integral of 0 over unit balanced (= 0)
    ∧ isBalanced (IsAntiderivative.integral
        (IsAntiderivative.const_anti (constCut 0 1)) unitBracket)
    -- (3) Symbolic FTC: integral = fluxAlong (def-eq)
    ∧ ∀ F sF f db (hF : IsAntiderivative F sF f),
        IsAntiderivative.integral hF db = fluxAlong F db :=
  ⟨IsAntiderivative.integral_one_unit,
   IsAntiderivative.integral_zero_unit_balanced,
   fun _ _ _ _ _ => rfl⟩

end E213.Lib.Math.Analysis.Integration.IntegralViaAnti
