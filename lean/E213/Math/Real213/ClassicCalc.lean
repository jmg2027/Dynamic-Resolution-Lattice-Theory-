import E213.Math.Real213.FluxPassthroughCatalog
import E213.Math.Real213.DifferentiableInstances

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.DyadicBracket
import E213.Math.Real213.DyadicTrajectory
import E213.Math.Real213.FluxCochain
import E213.Math.Real213.FluxCut
import E213.Math.Real213.FluxDivergence
import E213.Math.Real213.FluxMVT
import E213.Math.Real213.FluxPassthroughClass
import E213.Math.Real213.IsDifferentiable
/-!
# Classical calculus structure — `ClassicCalc_at`

`ClassicCalc_at f` bundles `IsDifferentiable f` (derivative computation)
+ `Passthrough_at f` (MVT/FTC at unit) into a single class.

Anything constructed as `ClassicCalc_at` automatically gets:
  - explicit derivative function
  - polynomial-style modulus `n*k`
  - MVT propEq at unit
  - FTC bridge propEq at unit

```
ClassicCalc_at f := { diff : IsDifferentiable f, pass : Passthrough_at f }
```

## Polynomial instances (degrees 1-16 + generic)

| degree | instance         | derivative modulus |
|-------:|------------------|-------------------:|
|      1 | `id_calc`        | 0                  |
|      2 | `square_calc`    | k                  |
|      3 | `cube_calc`      | 2k                 |
|      4 | `quartic_calc`   | 3k                 |
|      5 | `quintic_calc`   | 4k                 |
|      6 | `sextic_calc`    | 5k                 |
|      7 | `septic_calc`    | 6k                 |
|      8 | `octic_calc`     | 7k                 |
|      9 | `nonic_calc`     | 8k                 |
|     10 | `decic_calc`     | 9k                 |
|     12 | `dodecic_calc`   | 11k                |
|     16 | `hexadecic_calc` | 15k                |
|  n + 1 | `cutPow_calc_at` | `n·k`              |

(Consolidated 2026-05-05 from 4 phase files: `ClassicCalc` [core +
deg 1-3] + `ClassicCalcHigher` [deg 4-8] + `ClassicCalcExtreme`
[deg 9, 10, 12, 16] + `ClassicCalcGeneric` [deg n+1].  Per-stage
capstone bundles dropped — instances + core methods remain.)
-/

namespace E213.Math.Real213.ClassicCalc

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.FluxPassthroughClass.FluxCut (Passthrough_at)
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
open E213.Math.Real213.DifferentiableHighOrder
  (nonicIsDifferentiable decicIsDifferentiable
   dodecicIsDifferentiable hexadecicIsDifferentiable)

/-- `ClassicCalc_at f`: differentiable + passthrough at unit, pointwise PURE. -/
structure ClassicCalc_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  diff : IsDifferentiable f
  pass : Passthrough_at f

namespace ClassicCalc_at

open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough_at
  (id_pass cutPow_pass mul_pass)
open E213.Math.Real213.FluxPassthroughCatalog.FluxCut.Passthrough_at
  (square_pass cube_pass quartic_pass quintic_pass)

/-- Extract derivative. -/
def derivative {f} (cc : ClassicCalc_at f) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  cc.diff.derivative

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough_at
  (mvt_pure ftc_pure)

/-- MVT one-liner (fluxCutEq, PURE). -/
theorem mvt_pure {f} (cc : ClassicCalc_at f) :
    fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1)) :=
  Passthrough_at.mvt_pure cc.pass

/-- FTC bridge one-liner (fluxCutEq, PURE). -/
theorem ftc_pure {f} (cc : ClassicCalc_at f) :
    fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  Passthrough_at.ftc_pure cc.pass

end ClassicCalc_at

end E213.Math.Real213.ClassicCalc

namespace E213.Math.Real213.ClassicCalc.ClassicCalc_at

open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.IsDifferentiable (idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable)
open E213.Math.Real213.DifferentiableHighOrder
  (nonicIsDifferentiable decicIsDifferentiable
   dodecicIsDifferentiable hexadecicIsDifferentiable)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough_at
  (id_pass mul_pass)
open E213.Math.Real213.FluxPassthroughCatalog.FluxCut.Passthrough_at
  (square_pass cube_pass quartic_pass quintic_pass)

/-! ## Concrete polynomial chain (degrees 1-16). -/

/-- id (degree 1) ∈ ClassicCalc_at. -/
def id_calc : ClassicCalc_at id :=
  { diff := idIsDifferentiable, pass := id_pass }

/-- x² ∈ ClassicCalc_at. -/
def square_calc : ClassicCalc_at (fun x => cutMul x x) :=
  { diff := squareIsDifferentiable, pass := square_pass }

/-- x³ ∈ ClassicCalc_at. -/
def cube_calc : ClassicCalc_at (fun x => cutMul x (cutMul x x)) :=
  { diff := cubeIsDifferentiable, pass := cube_pass }

/-- x⁴ ∈ ClassicCalc_at. -/
def quartic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  { diff := quarticIsDifferentiable, pass := quartic_pass }

/-- x⁵ ∈ ClassicCalc_at. -/
def quintic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x x)
                                    (cutMul x (cutMul x x))) :=
  { diff := quinticIsDifferentiable, pass := quintic_pass }

/-- x⁶ ∈ ClassicCalc_at (cube · cube). -/
def sextic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x (cutMul x x))
                                    (cutMul x (cutMul x x))) :=
  { diff := sexticIsDifferentiable
    pass := mul_pass cube_pass cube_pass }

/-- x⁷ ∈ ClassicCalc_at (cube · quartic). -/
def septic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul x (cutMul x x))
                                    (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := septicIsDifferentiable
    pass := mul_pass cube_pass quartic_pass }

/-- x⁸ ∈ ClassicCalc_at (quartic · quartic). -/
def octic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                    (cutMul (cutMul x x) (cutMul x x))) :=
  { diff := octicIsDifferentiable
    pass := mul_pass quartic_pass quartic_pass }

/-- x⁹ ∈ ClassicCalc_at (quartic · quintic). -/
def nonic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  { diff := nonicIsDifferentiable
    pass := mul_pass quartic_pass quintic_pass }

/-- x¹⁰ ∈ ClassicCalc_at (quintic · quintic). -/
def decic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul (cutMul x x)
        (cutMul x (cutMul x x))) (cutMul (cutMul x x)
        (cutMul x (cutMul x x)))) :=
  { diff := decicIsDifferentiable
    pass := mul_pass quintic_pass quintic_pass }

/-- x¹² ∈ ClassicCalc_at (quartic · octic). -/
def dodecic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul (cutMul x x) (cutMul x x))
                (cutMul (cutMul x x) (cutMul x x)))) :=
  { diff := dodecicIsDifferentiable
    pass := mul_pass quartic_pass
              (mul_pass quartic_pass quartic_pass) }

/-- x¹⁶ ∈ ClassicCalc_at (octic · octic). -/
def hexadecic_calc :
    ClassicCalc_at (fun x => cutMul (cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x x)))
        (cutMul (cutMul (cutMul x x) (cutMul x x))
        (cutMul (cutMul x x) (cutMul x x)))) :=
  { diff := hexadecicIsDifferentiable
    pass := mul_pass
              (mul_pass quartic_pass quartic_pass)
              (mul_pass quartic_pass quartic_pass) }

open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.IsDifferentiable (cutPowFnIsDifferentiable)
open E213.Math.Real213.FluxPassthroughClass.FluxCut.Passthrough_at (cutPow_pass)
open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)

/-! ## Generic polynomial chain (any degree n + 1). -/

/-- ClassicCalc_at instance for `x ↦ x^(n+1)` at any natural n. -/
def cutPow_calc_at (n : Nat) :
    ClassicCalc_at (fun x => cutPow x (n+1)) :=
  { diff := cutPowFnIsDifferentiable (n+1)
    pass := cutPow_pass n }

/-- Generic MVT for `x^(n+1)`. -/
theorem cutPow_calc_mvt_pure (n : Nat) :
    fluxCutEq
      (localDivergence (fun x => cutPow x (n+1)) unitBracket)
      (ofCut (constCut 1 1)) :=
  (cutPow_calc_at n).mvt_pure

/-- Generic FTC bridge for `x^(n+1)`. -/
theorem cutPow_calc_ftc_pure (n : Nat) :
    fluxCutEq
      (localDivergence (fun x => cutPow x (n+1)) unitBracket)
      (fluxAlong (fun x => cutPow x (n+1)) unitBracket) :=
  (cutPow_calc_at n).ftc_pure

end E213.Math.Real213.ClassicCalc.ClassicCalc_at
