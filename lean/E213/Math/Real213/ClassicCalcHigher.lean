import E213.Math.Real213.ClassicCalc
import E213.Math.Real213.DifferentiableHigherPow

/-!
# Research.Real213ClassicCalcHigher

Phase BM: ClassicCalc to polynomial chain degrees 4-8.
Each gets explicit derivative + Passthrough + one-liner MVT/FTC.
-/

namespace E213.Math.Real213.ClassicCalcHigher

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.ClassicCalc (ClassicCalc)
open E213.Math.Real213.ClassicCalc.ClassicCalc
  (id_calc square_calc cube_calc mvt ftc)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough
  (id_pass cutPow_pass compose_pass mul_pass)
open E213.Math.Real213.FluxPassthroughCatalog.FluxCut.Passthrough
  (square_pass cube_pass quartic_pass quintic_pass)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable)

namespace ClassicCalc

/-- x⁴ ∈ ClassicCalc. -/
def quartic_calc :
    ClassicCalc (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  { diff := quarticIsDifferentiable
    pass := quartic_pass }

/-- x⁵ ∈ ClassicCalc. -/
def quintic_calc :
    ClassicCalc (fun x => cutMul (cutMul x x)
                                  (cutMul x (cutMul x x))) :=
  { diff := quinticIsDifferentiable
    pass := quintic_pass }

/-- x⁶ ∈ ClassicCalc (cube · cube). -/
def sextic_calc :
    ClassicCalc (fun x => cutMul (cutMul x (cutMul x x))
                                  (cutMul x (cutMul x x))) :=
  { diff := sexticIsDifferentiable
    pass := mul_pass
              cube_pass
              cube_pass }

/-- x⁷ ∈ ClassicCalc (cube · quartic). -/
def septic_calc :
    ClassicCalc (fun x => cutMul (cutMul x (cutMul x x))
                                  (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := septicIsDifferentiable
    pass := mul_pass
              cube_pass
              quartic_pass }

/-- x⁸ ∈ ClassicCalc (quartic · quartic). -/
def octic_calc :
    ClassicCalc (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                  (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := octicIsDifferentiable
    pass := mul_pass
              quartic_pass
              quartic_pass }

/-- Phase BM capstone: 4-8 polynomial chain in ClassicCalc. -/
theorem classic_calc_higher_capstone :
    localDivergence
        (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence
        (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence
        (fun x => cutMul (cutMul x (cutMul x x))
                         (cutMul x (cutMul x x))) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence
        (fun x => cutMul (cutMul x (cutMul x x))
                         (cutMul (cutMul x x) (cutMul x x))) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence
        (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                         (cutMul (cutMul x x) (cutMul x x))) unitBracket
        = ofCut (constCut 1 1) :=
  ⟨quartic_calc.mvt, quintic_calc.mvt, sextic_calc.mvt,
   septic_calc.mvt, octic_calc.mvt⟩

end ClassicCalc

namespace ClassicCalc_at

open E213.Math.Real213.ClassicCalc (ClassicCalc_at)
open E213.Math.Real213.ClassicCalc.ClassicCalc_at (square_calc cube_calc)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough_at
  (mul_pass)
open E213.Math.Real213.FluxPassthroughCatalog.FluxCut.Passthrough_at
  (square_pass cube_pass quartic_pass quintic_pass)

/-- x⁴ ∈ ClassicCalc_at — PURE pointwise. -/
def quartic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  { diff := quarticIsDifferentiable, pass := quartic_pass }

/-- x⁵ ∈ ClassicCalc_at — PURE pointwise. -/
def quintic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x x)
                                    (cutMul x (cutMul x x))) :=
  { diff := quinticIsDifferentiable, pass := quintic_pass }

/-- x⁶ ∈ ClassicCalc_at (cube · cube) — PURE pointwise. -/
def sextic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x (cutMul x x))
                                    (cutMul x (cutMul x x))) :=
  { diff := sexticIsDifferentiable
    pass := mul_pass cube_pass cube_pass }

/-- x⁷ ∈ ClassicCalc_at (cube · quartic) — PURE pointwise. -/
def septic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x (cutMul x x))
                                    (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := septicIsDifferentiable
    pass := mul_pass cube_pass quartic_pass }

/-- x⁸ ∈ ClassicCalc_at (quartic · quartic) — PURE pointwise. -/
def octic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                    (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := octicIsDifferentiable
    pass := mul_pass quartic_pass quartic_pass }

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)

/-- ★ Classic calc higher capstone (fluxCutEq, PURE):
    x⁴ through x⁸ all have MVT at unit. -/
theorem classic_calc_higher_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                               unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence
        (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x)))
        unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence
        (fun x => cutMul (cutMul x (cutMul x x))
                         (cutMul x (cutMul x x))) unitBracket)
        (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence
        (fun x => cutMul (cutMul x (cutMul x x))
                         (cutMul (cutMul x x) (cutMul x x))) unitBracket)
        (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence
        (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                         (cutMul (cutMul x x) (cutMul x x))) unitBracket)
        (ofCut (constCut 1 1)) :=
  ⟨quartic_calc.mvt_pure, quintic_calc.mvt_pure, sextic_calc.mvt_pure,
   septic_calc.mvt_pure, octic_calc.mvt_pure⟩

end ClassicCalc_at

end E213.Math.Real213.ClassicCalcHigher
