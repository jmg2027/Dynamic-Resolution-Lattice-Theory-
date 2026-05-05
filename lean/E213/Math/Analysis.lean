import E213.Math.Real213
import E213.Math.Analysis.Antiderivative
import E213.Math.Analysis.BracketCauchyModulus
import E213.Math.Analysis.CauchyComplete
import E213.Math.Analysis.ClassicAnti
import E213.Math.Analysis.ClassicCalc
import E213.Math.Analysis.ClassicCalcCombinators
import E213.Math.Analysis.ClassicCalcMid
import E213.Math.Analysis.ConcreteDerivativeModulus
import E213.Math.Analysis.ConsistentOracle
import E213.Math.Analysis.CubeDerivativeAtZero
import E213.Math.Analysis.CutGeomSeries
import E213.Math.Analysis.CutRiemann
import E213.Math.Analysis.CutSequence
import E213.Math.Analysis.CutSeries
import E213.Math.Analysis.DerivativeDepth
import E213.Math.Analysis.DerivativeForms
import E213.Math.Analysis.Diff
import E213.Math.Analysis.DifferentiableAffine
import E213.Math.Analysis.DifferentiableCompose
import E213.Math.Analysis.DifferentiableInstances
import E213.Math.Analysis.DifferentiableMid
import E213.Math.Analysis.DyadicBracket
import E213.Math.Analysis.DyadicRiemann
import E213.Math.Analysis.DyadicTrajectory
import E213.Math.Analysis.FTCRiemann
import E213.Math.Analysis.FluxCochain
import E213.Math.Analysis.FluxCut
import E213.Math.Analysis.FluxDivergence
import E213.Math.Analysis.FluxEquiv
import E213.Math.Analysis.FluxEquivOps
import E213.Math.Analysis.FluxFTC
import E213.Math.Analysis.FluxFTCPolynomial
import E213.Math.Analysis.FluxMVT
import E213.Math.Analysis.FluxMVTConcrete
import E213.Math.Analysis.FluxMVTPassthrough
import E213.Math.Analysis.FluxMVTPolynomial
import E213.Math.Analysis.FluxMVTPropagate
import E213.Math.Analysis.FluxMVTWitness
import E213.Math.Analysis.FluxMVTWitnessCombinators
import E213.Math.Analysis.FluxPassthroughCatalog
import E213.Math.Analysis.FluxPassthroughClass
import E213.Math.Analysis.FluxPolynomial
import E213.Math.Analysis.FluxSeries
import E213.Math.Analysis.HasDyadicMVTWitness
import E213.Math.Analysis.IVT
import E213.Math.Analysis.IndefiniteIntegral
import E213.Math.Analysis.IntegralDyadic
import E213.Math.Analysis.IntegralGeneralInt
import E213.Math.Analysis.IntegralIntInterval
import E213.Math.Analysis.IntegralProperties
import E213.Math.Analysis.IntegralViaAnti
import E213.Math.Analysis.Integration
import E213.Math.Analysis.IsDifferentiable
import E213.Math.Analysis.IsSmooth
import E213.Math.Analysis.MVTWitnessCatalog
import E213.Math.Analysis.MVTWitnessChain
import E213.Math.Analysis.ModulusCombiner
import E213.Math.Analysis.NewtonFirst
import E213.Math.Analysis.NewtonSecond
import E213.Math.Analysis.ODE
import E213.Math.Analysis.PhysicsBridgeNT2
import E213.Math.Analysis.PolySumDerivativeModulus
import E213.Math.Analysis.ResolutionDepth

/-! Spec-as-code entry point for `E213.Math.Analysis`.

  213-native analysis — calculus on top of `Math/Real213`.  Includes
  Bishop-style differential calculus, Riemann integration, the
  cohomological Mean Value Theorem (Flux form), Cauchy completeness,
  series, dyadic-search IVT, ODE, Newton's laws.

  Importing this module pulls in the Real213 base type AND all of
  Analysis on top.

  ## Sub-clusters (M5c will split into chapter sub-directories)

    * **Differentiation**: `IsDifferentiable`, `IsSmooth`, polynomial
      chain, derivatives, modulus combinators
    * **Integration**: `IsAntiderivative`, integral classes, Riemann,
      flux-FTC
    * **Mean-value theorem**: `FluxMVT.*`, dyadic witnesses,
      passthrough class
    * **Dyadic search / IVT**: `DyadicBracket` bisection, `ConsistentOracle`,
      `IVT`, search trajectories
    * **Cauchy / completeness**: `CauchyComplete`, bracket modulus
    * **Series**: `CutSeries`, `CutGeomSeries`, `FluxSeries`
    * **ODE / Newton**: linear ODE, Newton's first/second laws
    * **Bridge**: `PhysicsBridgeNT2` (NT=2 atomic block ↔ dyadic geometry)

  ## Status

  ∅-axiom standard on the production critical path.  63 files post
  M5b split.
-/
