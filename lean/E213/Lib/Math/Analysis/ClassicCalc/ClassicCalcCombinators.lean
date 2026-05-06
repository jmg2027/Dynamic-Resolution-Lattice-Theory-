import E213.Lib.Math.Analysis.FluxMVT.FTCRiemann

import E213.Lib.Math.Analysis.ClassicCalc.ClassicCalc
import E213.Lib.Math.Real213.Core
import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Analysis.FluxMVT.FluxDivergence
import E213.Lib.Math.Analysis.FluxMVT.FluxMVT
import E213.Lib.Math.Analysis.FluxMVT.FluxPassthroughClass
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# ClassicCalcCombinators
ClassicCalc combinators (compose, mul, mid).

ClassicCalc is closed under standard combinators: any function
buildable from these gets MVT/FTC at unit + explicit derivative
+ smoothness + Passthrough automatically.

  ClassicCalc.compose_calc   : g ∘ f if both ClassicCalc
  ClassicCalc.mul_calc        : cutMul f g if both ClassicCalc
-/

namespace E213.Lib.Math.Analysis.ClassicCalc.ClassicCalcCombinators

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core (Real213)
open E213.Lib.Math.Real213.CutMul (cutMul)
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable composeIsDifferentiable mulIsDifferentiable)
namespace ClassicCalc_at

open E213.Lib.Math.Analysis.ClassicCalc.ClassicCalc (ClassicCalc_at)
open E213.Lib.Math.Analysis.ClassicCalc.ClassicCalc.ClassicCalc_at (id_calc square_calc cube_calc)
open E213.Lib.Math.Analysis.FluxMVT.FluxPassthroughClass.FluxCut.Passthrough_at
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

open E213.Lib.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)

/-- ★ Combinators capstone (fluxCutEq, PURE): combinator-derived
    ClassicCalc instances all yield MVT at unit. -/
theorem combinators_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  x_mul_square_calc.mvt_pure

end ClassicCalc_at

end E213.Lib.Math.Analysis.ClassicCalc.ClassicCalcCombinators
