import E213.Math.Analysis.Differentiation.ConcreteDerivativeModulus
import E213.Math.Analysis.Differentiation.CubeDerivativeAtZero
import E213.Math.Analysis.Differentiation.DerivativeDepth
import E213.Math.Analysis.Differentiation.DerivativeForms
import E213.Math.Analysis.Differentiation.DifferenceQuotient
import E213.Math.Analysis.Differentiation.Differentiable
import E213.Math.Analysis.Differentiation.DifferentiableAffine
import E213.Math.Analysis.Differentiation.DifferentiableCompose
import E213.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Math.Analysis.Differentiation.DifferentiableMid
import E213.Math.Analysis.Differentiation.ModulusCombiner
import E213.Math.Analysis.Differentiation.PolySumDerivativeModulus
import E213.Math.Analysis.Differentiation.ResolutionDepth
import E213.Math.Analysis.Differentiation.Smooth

/-! Spec-as-code entry point for `E213.Math.Analysis.Differentiation`.

  Differential calculus on cuts.

  ## Type definitions

    * `Differentiable`           — Differentiable predicate
    * `DifferentiableMid`        — midpoint-localised variant
    * `DifferentiableInstances`  — concrete instances
    * `DifferentiableAffine`     — affine-function instance
    * `DifferentiableCompose`    — composition of differentiables
    * `Smooth`                   — `C^∞` smoothness predicate

  ## Derivatives

    * `DifferenceQuotient`       — difference-quotient builder
    * `DerivativeForms`          — pointwise derivative forms
    * `DerivativeDepth`          — derivative resolution depth
    * `ResolutionDepth`          — resolution-depth bookkeeping

  ## Concrete instances + supporting lemmas

    * `CubeDerivativeAtZero`         — d/dx[x³] at 0 = 0
    * `ConcreteDerivativeModulus`    — concrete-modulus witness
    * `PolySumDerivativeModulus`     — polynomial-sum derivative
    * `ModulusCombiner`              — modulus-combination utility
-/
