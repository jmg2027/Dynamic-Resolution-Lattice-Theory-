import E213.Research.Real213.CutBisectionAlgo
import E213.Research.Real213.CutDiffQuotient
import E213.Research.Real213.CutRiemann
import E213.Research.Real213.AsLensOutput
import E213.Research.Real213.RecurrenceLens
import E213.Research.Real213.ValidCut
import E213.Research.Real213.ValidCutOps
import E213.Research.Real213.CutMidMono
import E213.Research.Real213.IVTContainment
import E213.Research.Real213.Dyadic
import E213.Research.Real213.DyadicBracket
import E213.Research.Real213.IsSmooth
import E213.Research.Real213.ConsistentOracle
import E213.Research.Real213.DyadicRiemann
import E213.Research.Real213.PhaseJCapstone
import E213.Research.Real213.ResolutionDepth
import E213.Research.Real213.DyadicTrajectory
import E213.Research.Real213.PhaseLCapstone
import E213.Research.Real213.PhaseACMinimumProposition
import E213.Research.Real213.PhysicsBridgeNT2
import E213.Research.Real213.IsDifferentiable
import E213.Research.Real213.DerivativeForms
import E213.Research.Real213.DerivativeDepth
import E213.Research.Real213.PhaseADCapstone
import E213.Research.Real213.DifferentiableInstances
import E213.Research.Real213.PhaseAESuperCapstone
import E213.Research.Real213.DifferentiableHigherPow
import E213.Research.Real213.DifferentiationCapstone
import E213.Research.Real213.PhaseAHGrandCapstone
import E213.Research.Real213.DifferentiableAffine
import E213.Research.Real213.DifferentiableCompose
import E213.Research.Real213.DifferentiableHighOrder
import E213.Research.Real213.DifferentiableMid
import E213.Research.Real213.DifferentiableMegaCoverage
import E213.Research.Real213.PhaseANOmegaCapstone
import E213.Research.Real213.DerivativeDecide
import E213.Research.Real213.ConcreteDerivativeModulus
import E213.Research.Real213.ConcreteDerivativeModulusHigh
import E213.Research.Real213.ConcreteDerivativeModulusFinal
import E213.Research.Real213.ConcreteDerivativeMega
import E213.Research.Real213.PolySumDerivativeModulus
import E213.Research.Real213.ComposeDerivativeModulus
import E213.Research.Real213.FluxCut
import E213.Research.Real213.FluxCochain
import E213.Research.Real213.FluxDivergence
import E213.Research.Real213.FluxMVT
import E213.Research.Real213.FluxPolynomial
import E213.Research.Real213.FluxCohomologyCapstone
import E213.Research.Real213.FluxEquiv
import E213.Research.Real213.FluxEquivOps
import E213.Research.Real213.FluxMVTConcrete
import E213.Research.Real213.FluxFTC
import E213.Research.Real213.PhaseBACapstone
import E213.Research.Real213.FluxMVTPolynomial
import E213.Research.Real213.FluxFTCPolynomial
import E213.Research.Real213.FluxMVTHigh
import E213.Research.Real213.FluxMVTGeneric
import E213.Research.Real213.FluxMVTPassthrough
import E213.Research.Real213.FluxMVTApplications
import E213.Research.Real213.PhaseBHCapstone
import E213.Research.Real213.FluxMVTClosure
import E213.Research.Real213.FluxPassthroughClass
import E213.Research.Real213.FluxPassthroughCatalog
import E213.Research.Real213.ClassicCalc
import E213.Research.Real213.ClassicCalcHigher
import E213.Research.Real213.FluxSeries
import E213.Research.Real213.ClassicCalcExtreme
import E213.Research.Real213.ClassicCalcGeneric
import E213.Research.Real213.PhaseBQOmegaCapstone
import E213.Research.Real213.FluxMVTWitness
import E213.Research.Real213.ClassicCalcMid
import E213.Research.Real213.HasDyadicMVTWitness
import E213.Research.Real213.FluxMVTMore
import E213.Research.Real213.MVTWitnessCatalog
import E213.Research.Real213.MVTWitnessChain
import E213.Research.Real213.PhaseBXCapstone
import E213.Research.Real213.FTCRiemann
import E213.Research.Real213.PhaseBZMegaOmega
import E213.Research.Real213.FTCRiemannSquare
import E213.Research.Real213.FTCRiemannMid
import E213.Research.Real213.FTCRiemannGeneric
import E213.Research.Real213.FTCRiemannChain
import E213.Research.Real213.ClassicCalcCombinators
import E213.Research.Real213.FluxMVTNested
import E213.Research.Real213.FluxMVTPattern
import E213.Research.Real213.DerivativeShowcase
import E213.Research.Real213.FluxMVTNested2
import E213.Research.Real213.FluxMVTPropagate
import E213.Research.Real213.FluxMVTPropagateCompose
import E213.Research.Real213.PhaseCMFinalCapstone
import E213.Research.Real213.Antiderivative
import E213.Research.Real213.AntiderivativeCombinators
import E213.Research.Real213.AntiderivativeStructural
import E213.Research.Real213.IntegralViaAnti
import E213.Research.Real213.ClassicAnti
import E213.Research.Real213.PhaseCSCapstone
import E213.Research.Real213.IntegralProperties
import E213.Research.Real213.ODELinear
import E213.Research.Real213.ODECatalog
import E213.Research.Real213.ODESecondOrder
import E213.Research.Real213.NewtonFirst
import E213.Research.Real213.CubeDerivativeAtZero
import E213.Research.Real213.PhaseDAOmegaOmega
import E213.Research.Real213.NewtonSecond
import E213.Research.Real213.IndefiniteIntegral
import E213.Research.Real213.IntegralIntInterval
import E213.Research.Real213.IntegralGeneralInt
import E213.Research.Real213.IntegralDyadic
import E213.Research.Real213.GeomSeriesPartialSum
import E213.Research.Real213.ExpAtZero
import E213.Research.Real213.SinCosAtZero
import E213.Research.Real213.TranscendentalAtZero
import E213.Research.Real213.PhaseDKUltimate

/-!
# E213.Math.Analysis: analysis interfaces (IVT/Diff/Integration)

bisectStep / bisectN / bisectMidValue (IVT bisection algorithm).
differenceQuotient / DifferentiableModulus (differentiation).
riemannSumStep / RiemannIntegralData (integration).
RealAsLensOutput (User reframe formal).
RecurrenceLens (transcendental classification).

## Library status: SCAFFOLDED — interfaces + simple instances.

Full convergence/correctness proofs are a separate arc.
-/
