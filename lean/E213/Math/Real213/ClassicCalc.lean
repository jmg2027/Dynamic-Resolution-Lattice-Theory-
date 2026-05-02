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

/-- **ClassicCalc f**: differentiable AND passes through (0, 0), (1, 1). -/
structure ClassicCalc
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  diff : IsDifferentiable f
  pass : FluxCut.Passthrough f

namespace ClassicCalc

/-- id ∈ ClassicCalc with derivative 1, passes through endpoints. -/
def id_calc : ClassicCalc id :=
  { diff := idIsDifferentiable, pass := FluxCut.Passthrough.id_pass }

/-- x² ∈ ClassicCalc. -/
def square_calc : ClassicCalc (fun x => cutMul x x) :=
  { diff := squareIsDifferentiable
    pass := FluxCut.Passthrough.square_pass }

/-- x³ ∈ ClassicCalc. -/
def cube_calc : ClassicCalc (fun x => cutMul x (cutMul x x)) :=
  { diff := cubeIsDifferentiable
    pass := FluxCut.Passthrough.cube_pass }

/-- Extract MVT (one-liner). -/
theorem mvt {f} (cc : ClassicCalc f) :
    FluxCut.localDivergence f unitBracket
      = FluxCut.ofCut (constCut 1 1) :=
  cc.pass.mvt

/-- Extract FTC bridge (one-liner). -/
theorem ftc {f} (cc : ClassicCalc f) :
    FluxCut.localDivergence f unitBracket
      = FluxCut.fluxAlong f unitBracket :=
  cc.pass.ftc

/-- Extract derivative. -/
def derivative {f} (cc : ClassicCalc f) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  cc.diff.derivative

/-- ★ Phase BL capstone: ClassicCalc gives MVT + FTC at unit. -/
theorem classic_calc_capstone (f) (cc : ClassicCalc f) :
    -- (1) MVT propEq at unit
    FluxCut.localDivergence f unitBracket
       = FluxCut.ofCut (constCut 1 1)
    -- (2) FTC bridge propEq at unit
    ∧ FluxCut.localDivergence f unitBracket
       = FluxCut.fluxAlong f unitBracket
    -- (3) f passes through (0, 0)
    ∧ f (constCut 0 1) = constCut 0 1
    -- (4) f passes through (1, 1)
    ∧ f (constCut 1 1) = constCut 1 1 :=
  ⟨cc.mvt, cc.ftc, cc.pass.left, cc.pass.right⟩

end ClassicCalc

end E213.Math.Real213.ClassicCalc
