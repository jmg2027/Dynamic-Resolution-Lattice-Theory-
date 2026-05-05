import E213.Math.Analysis.Differentiation.Smooth
import E213.Math.Real213.Core

import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
/-!
# Research.Real213IsDifferentiable: differentiation filter

Extends `IsSmooth` with an explicit **derivative function** as
constructive data.  -1 scope: structure + instances; the
difference-quotient bound theorem is deferred to -3.

## Instances (AD-1)

  idIsDifferentiable       d/dx [x]    = 1
  constIsDifferentiable    d/dx [c]    = 0
  addIsDifferentiable      d/dx [f+g]  = f' + g'
  mulIsDifferentiable      d/dx [f·g]  = f'·g + f·g'
  composeIsDifferentiable  d/dx [g∘f]  = g'(f(x))·f'(x)
  cutPowFnIsDifferentiable polynomial via product rule
-/

namespace E213.Math.Analysis.Differentiation.Differentiable

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Analysis.Differentiation.Smooth (IsSmooth addIsSmooth composeIsSmooth constIsSmooth idIsSmooth mulIsSmooth)

/-- **Differentiability filter**: smoothness + explicit derivative. -/
structure IsDifferentiable (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    extends IsSmooth f where
  derivative : (Nat → Nat → Bool) → (Nat → Nat → Bool)
  derivativeSmooth : IsSmooth derivative

/-- Identity: d/dx [x] = 1. -/
def idIsDifferentiable : IsDifferentiable id where
  toIsSmooth := idIsSmooth
  derivative := constCutFn (constCut 1 1)
  derivativeSmooth := constIsSmooth (constCut 1 1)

/-- Constant: d/dx [c] = 0. -/
def constIsDifferentiable (c : Nat → Nat → Bool) :
    IsDifferentiable (constCutFn c) where
  toIsSmooth := constIsSmooth c
  derivative := constCutFn (constCut 0 1)
  derivativeSmooth := constIsSmooth (constCut 0 1)

/-- Sum rule: d/dx [f + g] = f' + g'. -/
def addIsDifferentiable {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) :
    IsDifferentiable (fun x => cutSum (f x) (g x)) where
  toIsSmooth := addIsSmooth sf.toIsSmooth sg.toIsSmooth
  derivative := fun x => cutSum (sf.derivative x) (sg.derivative x)
  derivativeSmooth := addIsSmooth sf.derivativeSmooth sg.derivativeSmooth

/-- Product rule: d/dx [f·g] = f'·g + f·g'. -/
def mulIsDifferentiable {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) :
    IsDifferentiable (fun x => cutMul (f x) (g x)) where
  toIsSmooth := mulIsSmooth sf.toIsSmooth sg.toIsSmooth
  derivative := fun x => cutSum (cutMul (sf.derivative x) (g x))
                                (cutMul (f x) (sg.derivative x))
  derivativeSmooth := addIsSmooth
    (mulIsSmooth sf.derivativeSmooth sg.toIsSmooth)
    (mulIsSmooth sf.toIsSmooth sg.derivativeSmooth)

/-- Chain rule: d/dx [g∘f] = g'(f(x)) · f'(x). -/
def composeIsDifferentiable {f g}
    (sf : IsDifferentiable f) (sg : IsDifferentiable g) :
    IsDifferentiable (g ∘ f) where
  toIsSmooth := composeIsSmooth sg.toIsSmooth sf.toIsSmooth
  derivative := fun x => cutMul (sg.derivative (f x)) (sf.derivative x)
  derivativeSmooth := mulIsSmooth
    (composeIsSmooth sg.derivativeSmooth sf.toIsSmooth)
    sf.derivativeSmooth

/-- Polynomial chain via product rule. -/
def cutPowFnIsDifferentiable : ∀ n, IsDifferentiable (fun x => cutPow x n)
  | 0 => constIsDifferentiable (constCut 1 1)
  | n+1 => mulIsDifferentiable (cutPowFnIsDifferentiable n) idIsDifferentiable

end E213.Math.Analysis.Differentiation.Differentiable
