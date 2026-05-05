import E213.Math.Real213.Antiderivative
import E213.Math.Real213.AsLensOutput
import E213.Math.Real213.BracketCauchyModulus
import E213.Math.Real213.CauchyComplete
import E213.Math.Real213.ClassicAnti
import E213.Math.Real213.ClassicCalc
import E213.Math.Real213.ClassicCalcCombinators
import E213.Math.Real213.ClassicCalcMid
import E213.Math.Real213.ConcreteDerivativeModulus
import E213.Math.Real213.ConsistentOracle
import E213.Math.Real213.ConstCutScale
import E213.Math.Real213.Core
import E213.Math.Real213.CubeDerivativeAtZero
import E213.Math.Real213.CutAlgebraStruct
import E213.Math.Real213.CutAlgebraic
import E213.Math.Real213.CutBinary
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutBisectionAlgo
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutDistance
import E213.Math.Real213.CutDouble
import E213.Math.Real213.CutFnData
import E213.Math.Real213.CutGeomSeries
import E213.Math.Real213.CutInv
import E213.Math.Real213.CutLatticeEq
import E213.Math.Real213.CutMaxMin
import E213.Math.Real213.CutMidMono
import E213.Math.Real213.CutMidSelf
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulComm
import E213.Math.Real213.CutMulConstConst
import E213.Math.Real213.CutMulDetermined
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutMulTest
import E213.Math.Real213.CutPoly
import E213.Math.Real213.CutPoset
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutPowConst
import E213.Math.Real213.CutRiemann
import E213.Math.Real213.CutScaleLattice
import E213.Math.Real213.CutSequence
import E213.Math.Real213.CutSeries
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumComm
import E213.Math.Real213.CutSumDetermined
import E213.Math.Real213.CutSumEq
import E213.Math.Real213.CutSumGeneral
import E213.Math.Real213.CutSumOne
import E213.Math.Real213.CutSumPointwise
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutSumZero
import E213.Math.Real213.DerivativeDepth
import E213.Math.Real213.DerivativeForms
import E213.Math.Real213.Diff
import E213.Math.Real213.DifferentiableAffine
import E213.Math.Real213.DifferentiableCompose
import E213.Math.Real213.DifferentiableInstances
import E213.Math.Real213.DifferentiableMid
import E213.Math.Real213.Dyadic
import E213.Math.Real213.DyadicBracket
import E213.Math.Real213.DyadicRiemann
import E213.Math.Real213.DyadicTrajectory
import E213.Math.Real213.Equiv
import E213.Math.Real213.FTCRiemann
import E213.Math.Real213.FluxCochain
import E213.Math.Real213.FluxCut
import E213.Math.Real213.FluxDivergence
import E213.Math.Real213.FluxEquiv
import E213.Math.Real213.FluxEquivOps
import E213.Math.Real213.FluxFTC
import E213.Math.Real213.FluxFTCPolynomial
import E213.Math.Real213.FluxMVT
import E213.Math.Real213.FluxMVTConcrete
import E213.Math.Real213.FluxMVTPassthrough
import E213.Math.Real213.FluxMVTPolynomial
import E213.Math.Real213.FluxMVTPropagate
import E213.Math.Real213.FluxMVTWitness
import E213.Math.Real213.FluxMVTWitnessCombinators
import E213.Math.Real213.FluxPassthroughCatalog
import E213.Math.Real213.FluxPassthroughClass
import E213.Math.Real213.FluxPolynomial
import E213.Math.Real213.FluxSeries
import E213.Math.Real213.Functions
import E213.Math.Real213.HasDyadicMVTWitness
import E213.Math.Real213.IVT
import E213.Math.Real213.IndefiniteIntegral
import E213.Math.Real213.IntegralDyadic
import E213.Math.Real213.IntegralGeneralInt
import E213.Math.Real213.IntegralIntInterval
import E213.Math.Real213.IntegralProperties
import E213.Math.Real213.IntegralViaAnti
import E213.Math.Real213.Integration
import E213.Math.Real213.IsDifferentiable
import E213.Math.Real213.IsSmooth
import E213.Math.Real213.MVTWitnessCatalog
import E213.Math.Real213.MVTWitnessChain
import E213.Math.Real213.MinimumProposition
import E213.Math.Real213.ModulusCombiner
import E213.Math.Real213.NewtonFirst
import E213.Math.Real213.NewtonSecond
import E213.Math.Real213.ODE
import E213.Math.Real213.PhysicsBridgeNT2
import E213.Math.Real213.PolySumDerivativeModulus
import E213.Math.Real213.ResolutionDepth
import E213.Math.Real213.Signed
import E213.Math.Real213.SignedSum
import E213.Math.Real213.ValidCut
import E213.Math.Real213.ValidCutOps

/-! Spec-as-code entry point for `E213.Math.Real213`.

  213-native real-number library — Bishop-style constructive analysis
  on the dyadic cut representation.  Importing this single module
  pulls in the entire Real213 library:

    * **Type-level foundation**: `Real213` type + Equiv + Order + Sign
    * **Cut algebra**: `cutSum`, `cutMul`, `cutPow`, `cutBisection`, etc.
    * **Series + Cauchy**: partial sums + completeness (direct construction)
    * **Differentiation**: `IsDifferentiable` + `IsSmooth` + concrete chain
    * **Integration**: `IsAntiderivative` + integral classes + flux-FTC
    * **Mean-value theorem**: `FluxMVT` cohomological form + dyadic witnesses
    * **Dyadic search**: `DyadicBracket` bisection + IVT
    * **ODE / Newton**: linear ODE + Newton's first/second laws
    * **Bridge**: physics-track NT=2 atomic block ↔ dyadic geometry

  Status: ∅-axiom standard on the production critical path; pre-M5
  research scaffolds (108 → after M5 cleanup) referencing
  session-27-deleted function-eq theorems were removed.

  Per-chapter umbrellas (`Math/Foundation`, `Math/CutOps`,
  `Math/Cauchy`, `Math/Series`, `Math/Analysis`, `Math/Analysis213`)
  remain as topical sub-imports for consumers needing only a slice.
-/
