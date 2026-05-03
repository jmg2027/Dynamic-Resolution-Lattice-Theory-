import E213.Math.Real213.FTCRiemannChain

/-!
# Research.Real213ClassicCalcCombinators

Phase CE: ClassicCalc combinators (compose, mul, mid).

ClassicCalc is closed under standard combinators: any function
buildable from these gets MVT/FTC at unit + explicit derivative
+ smoothness + Passthrough automatically.

  ClassicCalc.compose_calc   : g ∘ f if both ClassicCalc
  ClassicCalc.mul_calc        : cutMul f g if both ClassicCalc
-/

namespace E213.Math.Real213.ClassicCalcCombinators

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable composeIsDifferentiable mulIsDifferentiable)
open E213.Math.Real213.ClassicCalc (ClassicCalc)
open E213.Math.Real213.ClassicCalc.ClassicCalc
  (id_calc square_calc cube_calc mvt ftc)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough
  (compose_pass mul_pass)

namespace ClassicCalc

/-- ClassicCalc closure under composition. -/
def compose_calc {f g} (cf : ClassicCalc f) (cg : ClassicCalc g) :
    ClassicCalc (g ∘ f) :=
  { diff := composeIsDifferentiable cf.diff cg.diff
    pass := compose_pass cf.pass cg.pass }

/-- ClassicCalc closure under product. -/
def mul_calc {f g} (cf : ClassicCalc f) (cg : ClassicCalc g) :
    ClassicCalc (fun x => cutMul (f x) (g x)) :=
  { diff := mulIsDifferentiable cf.diff cg.diff
    pass := mul_pass cf.pass cg.pass }

/-- id ∘ x² ∈ ClassicCalc. -/
def id_compose_square_calc :
    ClassicCalc ((fun x => x) ∘ (fun x => cutMul x x)) :=
  compose_calc square_calc id_calc

/-- x² ∘ x² (= x⁴ as composition) ∈ ClassicCalc. -/
def square_compose_square_calc :
    ClassicCalc ((fun x => cutMul x x) ∘ (fun x => cutMul x x)) :=
  compose_calc square_calc square_calc

/-- x · x² (= x³ as product) ∈ ClassicCalc. -/
def x_mul_square_calc :
    ClassicCalc (fun x => cutMul x (cutMul x x)) :=
  mul_calc id_calc square_calc

/-- Phase CE capstone: combinator-derived ClassicCalc instances yield MVT. -/
theorem combinators_capstone :
    localDivergence ((fun x => x) ∘ (fun x => cutMul x x)) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence ((fun x => cutMul x x) ∘ (fun x => cutMul x x))
        unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul x (cutMul x x))
        unitBracket = ofCut (constCut 1 1) :=
  ⟨id_compose_square_calc.mvt,
   square_compose_square_calc.mvt,
   x_mul_square_calc.mvt⟩

end ClassicCalc

namespace ClassicCalc_at

open E213.Math.Real213.ClassicCalc (ClassicCalc_at)
open E213.Math.Real213.ClassicCalc.ClassicCalc_at (id_calc square_calc cube_calc)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough_at
  renaming compose_pass → compose_pass_at, mul_pass → mul_pass_at

/-- ClassicCalc_at closure under product (PURE pointwise). -/
def mul_calc {f g} (cf : ClassicCalc_at f) (cg : ClassicCalc_at g) :
    ClassicCalc_at (fun x => cutMul (f x) (g x)) :=
  { diff := mulIsDifferentiable cf.diff cg.diff
    pass := mul_pass_at cf.pass cg.pass }

/-- x · x² ∈ ClassicCalc_at — PURE pointwise. -/
def x_mul_square_calc :
    ClassicCalc_at (fun x => cutMul x (cutMul x x)) :=
  mul_calc id_calc square_calc

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)

/-- ★ Combinators capstone (fluxCutEq, PURE): combinator-derived
    ClassicCalc instances all yield MVT at unit. -/
theorem combinators_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  x_mul_square_calc.mvt_pure

end ClassicCalc_at

end E213.Math.Real213.ClassicCalcCombinators
