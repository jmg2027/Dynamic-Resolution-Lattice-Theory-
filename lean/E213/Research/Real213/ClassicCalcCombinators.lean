import E213.Research.Real213.FTCRiemannChain

/-!
# Research.Real213ClassicCalcCombinators

Phase CE: ClassicCalc combinators (compose, mul, mid).

ClassicCalc is closed under standard combinators: any function
buildable from these gets MVT/FTC at unit + explicit derivative
+ smoothness + Passthrough automatically.

  ClassicCalc.compose_calc   : g ∘ f if both ClassicCalc
  ClassicCalc.mul_calc        : cutMul f g if both ClassicCalc
-/

namespace E213.Research.Real213.ClassicCalcCombinators

open E213.Firmware E213.Hypervisor

namespace ClassicCalc

/-- ClassicCalc closure under composition. -/
def compose_calc {f g} (cf : ClassicCalc f) (cg : ClassicCalc g) :
    ClassicCalc (g ∘ f) :=
  { diff := composeIsDifferentiable cf.diff cg.diff
    pass := FluxCut.Passthrough.compose_pass cf.pass cg.pass }

/-- ClassicCalc closure under product. -/
def mul_calc {f g} (cf : ClassicCalc f) (cg : ClassicCalc g) :
    ClassicCalc (fun x => cutMul (f x) (g x)) :=
  { diff := mulIsDifferentiable cf.diff cg.diff
    pass := FluxCut.Passthrough.mul_pass cf.pass cg.pass }

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
    FluxCut.localDivergence ((fun x => x) ∘ (fun x => cutMul x x)) unitBracket
        = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence ((fun x => cutMul x x) ∘ (fun x => cutMul x x))
        unitBracket = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence (fun x => cutMul x (cutMul x x))
        unitBracket = FluxCut.ofCut (constCut 1 1) :=
  ⟨id_compose_square_calc.mvt,
   square_compose_square_calc.mvt,
   x_mul_square_calc.mvt⟩

end ClassicCalc

end E213.Research.Real213.ClassicCalcCombinators
