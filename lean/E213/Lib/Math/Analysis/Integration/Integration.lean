import E213.Lib.Math.Analysis.Differentiation.DifferenceQuotient

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# Real213Integration: Riemann integration

Partition + Cauchy sequence form limit from Riemann sum.

## Definition

For continuous f : CutFunction on bracket [a, b]:
∫[a, b] f := limit of Riemann sums over n-partition.

## Status of this file

Interface — full algorithm (Riemann sum sequence + Cauchy completeness)
is separate work.  Lebesgue is outside the framework (measure theory absent).
-/

namespace E213.Lib.Math.Analysis.Integration.Integration

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- Riemann integration data. -/
structure RiemannIntegrable (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (a b : Nat → Nat → Bool) where
  integral : Nat → Nat → Bool  -- ∫[a, b] f, as a cut
  modulus : Nat → Nat → Nat  -- precision

/-- **Constant integration on the unit interval [0, 1]**:
    ∫[0, 1] c dx = c · (1 − 0) = c.  Concrete unit-interval witness with
    the integral cut equal to `c` itself.  The general form
    ∫[a, b] c dx = c · (b − a) requires cut subtraction (signed) and is
    a separate arc; specializing to `(a, b) = (0, 1)` gives the only
    case where `integral := c` is mathematically correct. -/
def unitConstRiemannIntegrable (c : Nat → Nat → Bool) :
    RiemannIntegrable (constCutFn c) (constCut 0 1) (constCut 1 1) where
  integral := c
  modulus := fun _ _ => 0

end E213.Lib.Math.Analysis.Integration.Integration
