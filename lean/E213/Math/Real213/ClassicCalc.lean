import E213.Math.Real213.FluxPassthroughCatalog
import E213.Math.Real213.DifferentiableInstances

/-!
# Research.Real213ClassicCalc

Phase BL: integrated **ClassicCalc** structure bundling
`IsDifferentiable` (derivative computation) + `Passthrough`
(MVT/FTC at unit) into a single class.

Anything constructed as ClassicCalc gets:
  - explicit derivative function
  - polynomial-style modulus n*k
  - MVT propEq at unit
  - FTC bridge propEq at unit

  ClassicCalc f := { diff : IsDifferentiable f, pass : Passthrough f }
-/

namespace E213.Math.Real213.ClassicCalc

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.FluxPassthroughClass.FluxCut (Passthrough)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough
  (id_pass cutPow_pass compose_pass mul_pass)
open E213.Math.Real213.FluxPassthroughCatalog.FluxCut.Passthrough
  (square_pass cube_pass quartic_pass quintic_pass)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)

/-- **ClassicCalc f**: differentiable AND passes through (0, 0), (1, 1). -/
structure ClassicCalc
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  diff : IsDifferentiable f
  pass : Passthrough f

namespace ClassicCalc

/-- id ∈ ClassicCalc with derivative 1, passes through endpoints. -/
def id_calc : ClassicCalc id :=
  { diff := idIsDifferentiable, pass := Passthrough.id_pass }

/-- x² ∈ ClassicCalc. -/
def square_calc : ClassicCalc (fun x => cutMul x x) :=
  { diff := squareIsDifferentiable
    pass := square_pass }

/-- x³ ∈ ClassicCalc. -/
def cube_calc : ClassicCalc (fun x => cutMul x (cutMul x x)) :=
  { diff := cubeIsDifferentiable
    pass := cube_pass }

/-- Extract MVT (one-liner). -/
theorem mvt {f} (cc : ClassicCalc f) :
    localDivergence f unitBracket
      = ofCut (constCut 1 1) :=
  cc.pass.mvt

/-- Extract FTC bridge (one-liner). -/
theorem ftc {f} (cc : ClassicCalc f) :
    localDivergence f unitBracket
      = fluxAlong f unitBracket :=
  cc.pass.ftc

/-- Extract derivative. -/
def derivative {f} (cc : ClassicCalc f) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  cc.diff.derivative

/-- ★ Phase BL capstone: ClassicCalc gives MVT + FTC at unit. -/
theorem classic_calc_capstone (f) (cc : ClassicCalc f) :
    -- (1) MVT propEq at unit
    localDivergence f unitBracket
       = ofCut (constCut 1 1)
    -- (2) FTC bridge propEq at unit
    ∧ localDivergence f unitBracket
       = fluxAlong f unitBracket
    -- (3) f passes through (0, 0)
    ∧ f (constCut 0 1) = constCut 0 1
    -- (4) f passes through (1, 1)
    ∧ f (constCut 1 1) = constCut 1 1 :=
  ⟨cc.mvt, cc.ftc, cc.pass.left, cc.pass.right⟩

end ClassicCalc

end E213.Math.Real213.ClassicCalc
