import E213.Math.Analysis.DifferentiableInstances

import E213.Math.Real213.Core
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DifferentiableMid
import E213.Math.Analysis.DyadicTrajectory
import E213.Math.Analysis.FluxCochain
import E213.Math.Analysis.FluxCut
import E213.Math.Analysis.FluxFTC
import E213.Math.Analysis.IsDifferentiable
/-!
# Antiderivative class — `IsAntiderivative`

A function `F` is an antiderivative of `f` when `F`'s derivative
equals `f`.  Captures the integration ↔ differentiation duality in
213-native form.

```
IsAntiderivative F sf f := { eq : sf.derivative = f }
```

## Three axes (sub-namespaces preserved)

  * `E213.Math.Analysis.Antiderivative`            — definition + atomic instances
  * `E213.Math.Analysis.AntiderivativeCombinators` — mid / add / mul combinators
  * `E213.Math.Analysis.AntiderivativeStructural`  — every IsDifferentiable yields one

(Consolidated 2026-05-05 from 3 phase files: Antiderivative [Phase CN]
+ AntiderivativeCombinators [Phase CO] + AntiderivativeStructural
[Phase CP].  Per-stage capstone bundles dropped.)
-/

namespace E213.Math.Analysis.Antiderivative

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Analysis.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Analysis.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)

/-- F is differentiable and its derivative equals f. -/
structure IsAntiderivative
    (F : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sF : IsDifferentiable F)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  eq : sF.derivative = f

/-- PURE pointwise variant: replaces function-eq `eq` with pointwise `eq_at`. -/
structure IsAntiderivative_at
    (F : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sF : IsDifferentiable F)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  eq_at : ∀ x m k, sF.derivative x m k = f x m k

namespace IsAntiderivative

/-- id is antiderivative of constant 1. -/
def id_anti : IsAntiderivative id idIsDifferentiable
    (constCutFn (constCut 1 1)) :=
  { eq := rfl }

/-- Constant function c is antiderivative of constant 0. -/
def const_anti (c : Nat → Nat → Bool) :
    IsAntiderivative (constCutFn c) (constIsDifferentiable c)
      (constCutFn (constCut 0 1)) :=
  { eq := rfl }

end IsAntiderivative

namespace IsAntiderivative_at

/-- id is antiderivative of constant 1 (PURE pointwise). -/
def id_anti_at : IsAntiderivative_at id idIsDifferentiable
    (constCutFn (constCut 1 1)) :=
  { eq_at := fun _ _ _ => rfl }

/-- Constant c is antiderivative of constant 0 (PURE pointwise). -/
def const_anti_at (c : Nat → Nat → Bool) :
    IsAntiderivative_at (constCutFn c) (constIsDifferentiable c)
      (constCutFn (constCut 0 1)) :=
  { eq_at := fun _ _ _ => rfl }

end IsAntiderivative_at

end E213.Math.Analysis.Antiderivative

namespace E213.Math.Analysis.AntiderivativeCombinators

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.IsDifferentiable
  (IsDifferentiable idIsDifferentiable addIsDifferentiable)
open E213.Math.Analysis.DifferentiableMid (midIsDifferentiable)
open E213.Math.Analysis.Antiderivative (IsAntiderivative)
open E213.Math.Analysis.Antiderivative.IsAntiderivative (id_anti)

namespace IsAntiderivative

/-- midpoint combinator: mid(F, G) is antiderivative of mid(f, g). -/
def mid_anti {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g) :
    IsAntiderivative (fun x => cutMid (F x) (G x))
                      (midIsDifferentiable sF sG)
                      (fun x => cutMid (f x) (g x)) :=
  { eq := by
      show (fun x => cutMid (sF.derivative x) (sG.derivative x))
           = (fun x => cutMid (f x) (g x))
      rw [hF.eq, hG.eq] }

/-- Sum combinator: F + G is antiderivative of f + g. -/
def add_anti {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g) :
    IsAntiderivative (fun x => cutSum (F x) (G x))
                      (addIsDifferentiable sF sG)
                      (fun x => cutSum (f x) (g x)) :=
  { eq := by
      show (fun x => cutSum (sF.derivative x) (sG.derivative x))
           = (fun x => cutSum (f x) (g x))
      rw [hF.eq, hG.eq] }

/-- mid(id, id) is antiderivative of mid(1, 1). -/
def mid_id_id_anti :
    IsAntiderivative (fun x => cutMid x x)
                      (midIsDifferentiable idIsDifferentiable idIsDifferentiable)
                      (fun x => cutMid (constCut 1 1) (constCut 1 1)) :=
  mid_anti id_anti id_anti

end IsAntiderivative

end E213.Math.Analysis.AntiderivativeCombinators

namespace E213.Math.Analysis.AntiderivativeStructural

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.IsDifferentiable (IsDifferentiable)
open E213.Math.Analysis.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable)
open E213.Math.Analysis.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Analysis.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.Antiderivative (IsAntiderivative)
open E213.Math.Analysis.FluxFTC.FluxCut (fluxAlong_id_unitBracket)

namespace IsAntiderivative

/-- Every IsDifferentiable yields an antiderivative of its derivative. -/
def fromDifferentiable {F : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sF : IsDifferentiable F) : IsAntiderivative F sF sF.derivative :=
  { eq := rfl }

/-- Square is antiderivative of (1·x + x·1). -/
def square_anti :
    IsAntiderivative (fun x => cutMul x x) squareIsDifferentiable
      (fun x => cutSum (cutMul (constCut 1 1) x) (cutMul x (constCut 1 1))) :=
  fromDifferentiable squareIsDifferentiable

/-- Cube is antiderivative of its formal derivative (= 3x²). -/
def cube_anti :
    IsAntiderivative (fun x => cutMul x (cutMul x x)) cubeIsDifferentiable
      cubeIsDifferentiable.derivative :=
  fromDifferentiable cubeIsDifferentiable

/-- FTC connection: fluxAlong F at unit gives boundary value F(1) − F(0). -/
theorem fluxAlong_antiderivative_boundary
    {F sF f} (hF : IsAntiderivative F sF f) :
    fluxAlong F unitBracket
      = { forward := F (constCut 1 1), backward := F (constCut 0 1) } := rfl

end IsAntiderivative

end E213.Math.Analysis.AntiderivativeStructural
