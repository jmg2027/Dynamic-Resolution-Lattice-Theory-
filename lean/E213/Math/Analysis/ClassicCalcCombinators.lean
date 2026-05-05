import E213.Math.Analysis.FTCRiemann

import E213.Math.Analysis.ClassicCalc
import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DyadicBracket
import E213.Math.Analysis.DyadicTrajectory
import E213.Math.Analysis.FluxCut
import E213.Math.Analysis.FluxDivergence
import E213.Math.Analysis.FluxMVT
import E213.Math.Analysis.FluxPassthroughClass
import E213.Math.Analysis.IsDifferentiable
/-!
# Research.Real213ClassicCalcCombinators

Phase CE: ClassicCalc combinators (compose, mul, mid).

ClassicCalc is closed under standard combinators: any function
buildable from these gets MVT/FTC at unit + explicit derivative
+ smoothness + Passthrough automatically.

  ClassicCalc.compose_calc   : g ∘ f if both ClassicCalc
  ClassicCalc.mul_calc        : cutMul f g if both ClassicCalc
-/

namespace E213.Math.Analysis.ClassicCalcCombinators

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.IsDifferentiable
  (IsDifferentiable composeIsDifferentiable mulIsDifferentiable)
namespace ClassicCalc_at

open E213.Math.Analysis.ClassicCalc (ClassicCalc_at)
open E213.Math.Analysis.ClassicCalc.ClassicCalc_at (id_calc square_calc cube_calc)
open E213.Math.Analysis.FluxPassthroughClass.FluxCut.Passthrough_at
  renaming mul_pass → mul_pass_at

/-- ClassicCalc_at closure under product (PURE pointwise). -/
def mul_calc {f g} (cf : ClassicCalc_at f) (cg : ClassicCalc_at g) :
    ClassicCalc_at (fun x => cutMul (f x) (g x)) :=
  { diff := mulIsDifferentiable cf.diff cg.diff
    pass := mul_pass_at cf.pass cg.pass }

/-- x · x² ∈ ClassicCalc_at — PURE pointwise. -/
def x_mul_square_calc :
    ClassicCalc_at (fun x => cutMul x (cutMul x x)) :=
  mul_calc id_calc square_calc

open E213.Math.Analysis.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Analysis.FluxCut.FluxCut (ofCut)

/-- ★ Combinators capstone (fluxCutEq, PURE): combinator-derived
    ClassicCalc instances all yield MVT at unit. -/
theorem combinators_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  x_mul_square_calc.mvt_pure

end ClassicCalc_at

end E213.Math.Analysis.ClassicCalcCombinators
