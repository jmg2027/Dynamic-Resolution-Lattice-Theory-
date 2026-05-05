import E213.Math.Analysis.Antiderivative

import E213.Math.Real213.Core
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DyadicBracket
import E213.Math.Analysis.DyadicTrajectory
import E213.Math.Analysis.FluxCochain
import E213.Math.Analysis.FluxCut
import E213.Math.Analysis.FluxFTC
/-!
# Research.Real213IntegralViaAnti

Phase CQ: ★ integration via antiderivative ★

Defines `integralViaAntiderivative`: given an IsAntiderivative
hypothesis, the "definite integral" of f over a bracket is the
flux of F along that bracket.

  ∫_a^b f dx = F(b) - F(a)  (cohomologically: fluxAlong F db)

This is the FTC at the symbolic level — integration becomes flux
of the antiderivative.
-/

namespace E213.Math.Analysis.IntegralViaAnti

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxCut (FluxCut)
open E213.Math.Analysis.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxCochain.FluxCut
  (fluxAlong isBalanced fluxAlong_const_isBalanced)
open E213.Math.Analysis.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.Antiderivative (IsAntiderivative)
open E213.Math.Analysis.Antiderivative.IsAntiderivative (id_anti const_anti)
open E213.Math.Analysis.FluxFTC.FluxCut (fluxAlong_id_unitBracket)

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

/-- Phase CQ capstone: integration via antiderivative. -/
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

end E213.Math.Analysis.IntegralViaAnti
