import E213.Lib.Math.Analysis.DyadicSearch.IVT

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutContinuity
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
/-!
# Real213Diff: Differentiation (declarative form, )

Bishop-style differentiation in 213 cut form.

## Definition (declarative)

f : CutFunction is differentiable at point p (cut) with derivative
f' (cut function) if difference quotient (f(p+h) - f(p))/h converges
to f'(p) as h → 0.

cut form: bound provided via explicit modulus N(m, k).

## Status of this file

Interface + types — full implementation is separate.
-/

namespace E213.Lib.Math.Analysis.Differentiation.DifferenceQuotient

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Bisection.CutContinuity (constCutFn)

/-- Differentiability hypothesis at a cut-point. -/
structure DifferentiableAt (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (p : Nat → Nat → Bool) where
  derivative : Nat → Nat → Bool  -- f'(p) cut
  modulus : Nat → Nat → Nat  -- precision modulus

/-- Derivative of constant function = 0 (declarative). -/
def constDifferentiable (c : Nat → Nat → Bool) (p : Nat → Nat → Bool) :
    DifferentiableAt (constCutFn c) p where
  derivative := constCut 0 1  -- "0/1" cut representation (always true)
  modulus := fun _ _ => 0

end E213.Lib.Math.Analysis.Differentiation.DifferenceQuotient
