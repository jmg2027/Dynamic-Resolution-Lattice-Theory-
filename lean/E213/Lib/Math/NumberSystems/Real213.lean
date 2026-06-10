import E213.Lib.Math.NumberSystems.Real213.Core.AsLensOutput
import E213.Lib.Math.NumberSystems.Real213.Mul.ConstCutScale
import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Core.CutAlgebraStruct
import E213.Lib.Math.NumberSystems.Real213.Mul.CutAlgebraic
import E213.Lib.Math.NumberSystems.Real213.Mul.CutBinary
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisectionAlgo
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutContinuity
import E213.Lib.Math.NumberSystems.Real213.Mul.CutDistance
import E213.Lib.Math.NumberSystems.Real213.Mul.CutDouble
import E213.Lib.Math.NumberSystems.Real213.Core.CutFnData
import E213.Lib.Math.NumberSystems.Real213.Mul.CutInv
import E213.Lib.Math.NumberSystems.Real213.Lattice.CutLatticeEq
import E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin
import E213.Lib.Math.NumberSystems.Real213.Lattice.CutMidMono
import E213.Lib.Math.NumberSystems.Real213.Lattice.CutMidSelf
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulComm
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulConstConst
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulDetermined
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulOne
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulTest
import E213.Lib.Math.NumberSystems.Real213.Mul.CutPoly
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
import E213.Lib.Math.NumberSystems.Real213.Mul.CutPow
import E213.Lib.Math.NumberSystems.Real213.Mul.CutPowConst
import E213.Lib.Math.NumberSystems.Real213.Lattice.CutScaleLattice
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumDetermined
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumEq
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumGeneral
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumOne
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumPointwise
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumZero
import E213.Lib.Math.NumberSystems.Real213.Core.Dyadic
import E213.Lib.Math.NumberSystems.Real213.Core.Equiv
import E213.Lib.Math.NumberSystems.Real213.Core.Functions
import E213.Lib.Math.NumberSystems.Real213.Core.MinimumProposition
import E213.Lib.Math.NumberSystems.Real213.Sum.Signed
import E213.Lib.Math.NumberSystems.Real213.Sum.SignedSum
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCut
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCutOps
import E213.Lib.Math.NumberSystems.Real213.ChainToCut
import E213.Lib.Math.NumberSystems.Real213.ObjectIsReadingScaleInvariant
import E213.Lib.Math.NumberSystems.Real213.PhiConvergence
import E213.Lib.Math.NumberSystems.Real213.PhiAsCut
import E213.Lib.Math.NumberSystems.Real213.PhiCutConvergents
import E213.Lib.Math.NumberSystems.Real213.PhiNormInvariant
import E213.Lib.Math.NumberSystems.Real213.FibCassiniNat
import E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit
import E213.Lib.Math.NumberSystems.Real213.PhiFrozenDynamic
import E213.Lib.Math.NumberSystems.Real213.ZeckendorfCarry
import E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit
import E213.Lib.Math.NumberSystems.Real213.MinkowskiCocycle
import E213.Lib.Math.NumberSystems.Real213.MinkowskiGoldenExtremal
import E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodIntegral
import E213.Lib.Math.NumberSystems.Real213.MinkowskiHigherWeightPeriod
import E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodRelations
import E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodPolynomial
import E213.Lib.Math.NumberSystems.Real213.MinkowskiModularSymbol
import E213.Lib.Math.NumberSystems.Real213.HolonomicReal
import E213.Lib.Math.NumberSystems.Real213.RateModulus
import E213.Lib.Math.NumberSystems.Real213.RateStratification
import E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake
import E213.Lib.Math.NumberSystems.Real213.LiouvilleModulus
import E213.Lib.Math.NumberSystems.Real213.CrossDetEqDenom
import E213.Lib.Math.NumberSystems.Real213.ReciprocalSeries
import E213.Lib.Math.NumberSystems.Real213.CrossDetConstDenom
import E213.Lib.Math.NumberSystems.Real213.GeometricThreshold
import E213.Lib.Math.NumberSystems.Real213.CompletabilityGrade
import E213.Lib.Math.NumberSystems.Real213.PresentationDependence
import E213.Lib.Math.NumberSystems.Real213.IntensionalCompletability
import E213.Lib.Math.NumberSystems.Real213.RefinedCompletabilityEngine
import E213.Lib.Math.NumberSystems.Real213.HeightTowerResidue
import E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor
import E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
import E213.Lib.Math.NumberSystems.Real213.SpiralLayer
import E213.Lib.Math.NumberSystems.Real213.SpiralCoordinate
import E213.Lib.Math.NumberSystems.Real213.ScalingOrbit
import E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm
import E213.Lib.Math.NumberSystems.Real213.SpiralRotationInvariant
import E213.Lib.Math.NumberSystems.Real213.GoldenFormMarkov
import E213.Lib.Math.NumberSystems.Real213.MarkovTree
import E213.Lib.Math.NumberSystems.Real213.MarkovUniqueness
import E213.Lib.Math.NumberSystems.Real213.MarkovCassiniBridge
import E213.Lib.Math.NumberSystems.Real213.ModularElliptic
import E213.Lib.Math.NumberSystems.Real213.FoldReflections
import E213.Lib.Math.NumberSystems.Real213.EllipticCycleFixtures
import E213.Lib.Math.NumberSystems.Real213.HyperbolicBoost
import E213.Lib.Math.NumberSystems.Real213.ParabolicTranslation
import E213.Lib.Math.NumberSystems.Real213.Mat2CayleyHamilton
import E213.Lib.Math.NumberSystems.Real213.Mat2Assoc
import E213.Lib.Math.NumberSystems.Real213.Mat2TraceRecurrence
import E213.Lib.Math.NumberSystems.Real213.GoldenAperiodic
import E213.Lib.Math.NumberSystems.Real213.EllipticTracePeriodic
import E213.Lib.Math.NumberSystems.Real213.UTracePeriodic
import E213.Lib.Math.NumberSystems.Real213.CrossDetTraceField
import E213.Lib.Math.NumberSystems.Real213.MarkovModularBridge
import E213.Lib.Math.NumberSystems.Real213.MarkovInjectivity
import E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
import E213.Lib.Math.NumberSystems.Real213.Continuant
import E213.Lib.Math.NumberSystems.Real213.ContinuantMarkov
import E213.Lib.Math.NumberSystems.Real213.MarkovUniquenessRaw
import E213.Lib.Math.NumberSystems.Real213.ModularGeodesicLens
import E213.Lib.Math.NumberSystems.Real213.LagrangeExtremes
import E213.Lib.Math.NumberSystems.Real213.PentagonGoldenTrace
import E213.Lib.Math.NumberSystems.Real213.HyperbolicEllipticTrace
import E213.Lib.Math.NumberSystems.Real213.TowerNativeCompleteness
import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCertifiedBracket
import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus
import E213.Lib.Math.NumberSystems.Real213.NuEscape
import E213.Lib.Math.NumberSystems.Real213.CutSumAssocB3
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpConvergents
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogCauchyConvCapstone
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutTrigModulus
import E213.Lib.Math.NumberSystems.Real213.ExpLog.PiCut
import E213.Lib.Math.NumberSystems.Real213.FifthValidCut
import E213.Lib.Math.NumberSystems.Real213.HalfValidCut
import E213.Lib.Math.NumberSystems.Real213.Mul.Mobius213CutMulNPhase3
import E213.Lib.Math.NumberSystems.Real213.OracleContinuity
import E213.Lib.Math.NumberSystems.Real213.PellFibCutBridge
import E213.Lib.Math.NumberSystems.Real213.ProbeTwistDynamics
import E213.Lib.Math.NumberSystems.Real213.ProbeTwistFixedPoint
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumNMixed
import E213.Lib.Math.NumberSystems.Real213.ThirdValidCut

/-! Spec-as-code entry point for `E213.Lib.Math.NumberSystems.Real213`.

  213-native real-number type — the residue of pointing applied to
  `Nat → Nat → Bool`, plus full cut-level rational arithmetic.

  ## Scope

  This umbrella imports the Real213 *core type and its algebra* —
  what 213-native real numbers **are**, before any analysis is done
  on top.  Calculus (Differentiation, Integration, Flux-MVT, ODE,
  Cauchy completeness, Series) lives in a separate sibling tree:
  `Math/Analysis.lean`.

  ## Sub-clusters

    * **Type-level foundation**: `Real213` type + `Equiv` + `MinimumProposition`
    * **Cut algebra**: `cutSum`, `cutMul`, `cutPow`, `cutInv`, `cutBisection`,
      `cutPoset` (lattice ops), and their commutativity / determinism /
      pointwise lemmas
    * **Validation**: `ValidCut`, `ValidCutOps`
    * **Signed cuts**: `Signed`, `SignedSum`
    * **Dyadic representation**: `Dyadic` (basic; bracket/Riemann/trajectory
      live in `Math/Analysis/`)
    * **Lens output**: `AsLensOutput`, `Functions`

  ## Status

  ∅-axiom standard on the production critical path.  44 files post
  M5b split.
-/
