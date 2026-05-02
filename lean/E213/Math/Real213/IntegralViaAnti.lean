import E213.Math.Real213.AntiderivativeStructural

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

namespace E213.Math.Real213.IntegralViaAnti

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)

namespace IsAntiderivative

/-- ★ Definite integral via antiderivative: F's flux along the bracket. -/
def integral {F sF f} (_hF : IsAntiderivative F sF f)
    (db : DyadicBracket) : FluxCut :=
  FluxCut.fluxAlong F db

/-- ★ FTC at symbolic level: integral hF db = fluxAlong F db (def). -/
theorem integral_eq_flux {F sF f} (hF : IsAntiderivative F sF f)
    (db : DyadicBracket) :
    integral hF db = FluxCut.fluxAlong F db := rfl

/-- ★ Integral of constant 1 over unit (via id antideriv) = 1 cohomologically. -/
theorem integral_one_unit :
    integral id_anti unitBracket = FluxCut.ofCut (constCut 1 1) :=
  FluxCut.fluxAlong_id_unitBracket

/-- ★ Integral of constant 0 over unit (via constant antideriv) is balanced. -/
theorem integral_zero_unit_balanced :
    FluxCut.isBalanced (integral (const_anti (constCut 0 1)) unitBracket) :=
  FluxCut.fluxAlong_const_isBalanced (constCut 0 1) unitBracket

end IsAntiderivative

/-- Phase CQ capstone: integration via antiderivative. -/
theorem integral_via_anti_capstone :
    -- (1) Integral of 1 over unit = 1 (in ofCut form)
    IsAntiderivative.integral IsAntiderivative.id_anti unitBracket
        = FluxCut.ofCut (constCut 1 1)
    -- (2) Integral of 0 over unit balanced (= 0)
    ∧ FluxCut.isBalanced (IsAntiderivative.integral
        (IsAntiderivative.const_anti (constCut 0 1)) unitBracket)
    -- (3) Symbolic FTC: integral = fluxAlong (def-eq)
    ∧ ∀ F sF f db (hF : IsAntiderivative F sF f),
        IsAntiderivative.integral hF db = FluxCut.fluxAlong F db :=
  ⟨IsAntiderivative.integral_one_unit,
   IsAntiderivative.integral_zero_unit_balanced,
   fun _ _ _ _ _ => rfl⟩

end E213.Math.Real213.IntegralViaAnti
