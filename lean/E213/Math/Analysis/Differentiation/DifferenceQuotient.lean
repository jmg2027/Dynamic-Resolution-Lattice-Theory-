import E213.Math.Analysis.DyadicSearch.IVT

import E213.Math.Real213.Core
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutSumTest
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

namespace E213.Math.Analysis.Differentiation.DifferenceQuotient

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)

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

end E213.Math.Analysis.Differentiation.DifferenceQuotient
