# `Lib/Math/Analysis/Differentiation/` — differential calculus on cuts

Differentiable predicate, derivative forms, and concrete instances
on Real213 cuts.  Modulus-tracked (resolution-aware) differentiation.

## Files (14)

### Predicate (6)
  - `Differentiable.lean`            — base `Differentiable` predicate
  - `DifferentiableMid.lean`         — midpoint-localised variant
  - `DifferentiableInstances.lean`   — concrete instances
  - `DifferentiableAffine.lean`      — affine-function instance
  - `DifferentiableCompose.lean`     — composition of differentiables
  - `Smooth.lean`                    — `C^∞` smoothness predicate

### Derivative forms (4)
  - `DifferenceQuotient.lean`        — difference-quotient builder
  - `DerivativeForms.lean`           — pointwise derivative forms
  - `DerivativeDepth.lean`           — derivative resolution depth
  - `ResolutionDepth.lean`           — resolution-depth bookkeeping

### Concrete + supporting (4)
  - `CubeDerivativeAtZero.lean`      — d/dx[x³] at 0 = 0
  - `ConcreteDerivativeModulus.lean` — concrete-modulus witness
  - `PolySumDerivativeModulus.lean`  — polynomial-sum derivative
  - `ModulusCombiner.lean`           — modulus-combination utility

## Where to add new files

  - New differentiable instance  → `Differentiable<name>.lean`
  - New derivative form          → `Derivative<name>.lean`
  - Modulus / resolution detail  → `ResolutionDepth` / `Modulus*`
  - Concrete numeric example     → `<func>DerivativeAt<point>.lean`
