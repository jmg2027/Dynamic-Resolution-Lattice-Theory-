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
import E213.Lib.Math.NumberSystems.Real213.Core.CutNoFiniteCert
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
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiConvergence
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiCutConvergents
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiNormInvariant
import E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiCauchyLimit
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiFrozenDynamic
import E213.Lib.Math.NumberSystems.Real213.Phi.ZeckendorfCarry
import E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit
import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiCocycle
import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiGoldenExtremal
import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiPeriodIntegral
import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiHigherWeightPeriod
import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiPeriodRelations
import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiPeriodPolynomial
import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiModularSymbol
import E213.Lib.Math.NumberSystems.Real213.HolonomicReal
import E213.Lib.Math.NumberSystems.Real213.Zeta3Cut
import E213.Lib.Math.NumberSystems.Real213.Zeta3Apery
import E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut
import E213.Lib.Math.NumberSystems.Real213.Modulus.ModulusComposition
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateHierarchy
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateComparison
import E213.Lib.Math.NumberSystems.Real213.Modulus.DegreeCriterion
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateArithmetic
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateProduct
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateAffine
import E213.Lib.Math.NumberSystems.Real213.Modulus.RatePower
import E213.Lib.Math.NumberSystems.Real213.Modulus.PointingLimit
import E213.Lib.Math.NumberSystems.Real213.Modulus.BestApproximation
import E213.Lib.Math.NumberSystems.Real213.Modulus.BracketModulus
import E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetOvertake
import E213.Lib.Math.NumberSystems.Real213.Modulus.LiouvilleModulus
import E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetEqDenom
import E213.Lib.Math.NumberSystems.Real213.ReciprocalSeries
import E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetConstDenom
import E213.Lib.Math.NumberSystems.Real213.Completability.GeometricThreshold
import E213.Lib.Math.NumberSystems.Real213.Completability.CompletabilityGrade
import E213.Lib.Math.NumberSystems.Real213.PresentationDependence
import E213.Lib.Math.NumberSystems.Real213.Completability.IntensionalCompletability
import E213.Lib.Math.NumberSystems.Real213.Completability.RefinedCompletabilityEngine
import E213.Lib.Math.NumberSystems.Real213.Completability.HeightTowerResidue
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuedFractionFloor
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuedFractionModulus
import E213.Lib.Math.NumberSystems.Real213.Spiral.SpiralLayer
import E213.Lib.Math.NumberSystems.Real213.Spiral.SpiralCoordinate
import E213.Lib.Math.NumberSystems.Real213.Spiral.ScalingOrbit
import E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm
import E213.Lib.Math.NumberSystems.Real213.Spiral.SpiralRotationInvariant
import E213.Lib.Math.NumberSystems.Real213.Markov.GoldenFormMarkov
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovTree
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniqueness
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovCassiniBridge
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FoldReflections
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.EllipticCycleFixtures
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicBoost
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ParabolicTranslation
import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2CayleyHamilton
import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Adjugate
import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc
import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyOrderLaw
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyFreeness
import E213.Lib.Math.NumberSystems.Real213.Phi.GoldenAperiodic
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FiniteOrderSpectrum
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.EllipticTracePeriodic
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.UTracePeriodic
import E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetTraceField
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovModularBridge
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovInjectivity
import E213.Lib.Math.NumberSystems.Real213.Markov.SternBrocotMarkov
import E213.Lib.Math.NumberSystems.Real213.Markov.UnimodularSynthesis
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentCoprime
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentRecurrence
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentGrowth
import E213.Lib.Math.NumberSystems.Real213.Markov.ContinuantMarkov
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniquenessRaw
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovDescentSchema
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularGeodesicLens
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.LagrangeExtremes
import E213.Lib.Math.NumberSystems.Real213.Phi.PentagonGoldenTrace
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace
import E213.Lib.Math.NumberSystems.Real213.Completability.TowerNativeCompleteness
import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCertifiedBracket
import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus
import E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpUnitModulus
import E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpRationalCut
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertOrder
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMasterId
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertBridge
import E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpMoebius
import E213.Lib.Math.NumberSystems.Real213.ExpLog.PiMeasureModulus
import E213.Lib.Math.NumberSystems.Real213.NuEscape
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumAssocB3
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpConvergents
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogCauchyConvCapstone
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutTrigModulus
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpDerivative
import E213.Lib.Math.NumberSystems.Real213.ExpLog.PiCut
import E213.Lib.Math.NumberSystems.Real213.ValidCut.FifthValidCut
import E213.Lib.Math.NumberSystems.Real213.ValidCut.HalfValidCut
import E213.Lib.Math.NumberSystems.Real213.Mul.Mobius213CutMulNPhase3
import E213.Lib.Math.NumberSystems.Real213.OracleContinuity
import E213.Lib.Math.NumberSystems.Real213.Phi.PellFibCutBridge
import E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistDynamics
import E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistFixedPoint
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumNMixed
import E213.Lib.Math.NumberSystems.Real213.ValidCut.ThirdValidCut

/-! Spec-as-code entry point for `E213.Lib.Math.NumberSystems.Real213`.

  213-native real-number type — the residue of pointing applied to
  `Nat → Nat → Bool`, plus full cut-level rational arithmetic.

  ## Scope

  This umbrella imports the Real213 *core type and its algebra* —
  what 213-native real numbers **are**, before any analysis is done
  on top.  Calculus (Differentiation, Integration, Flux-MVT, ODE,
  Cauchy completeness, Series) lives in a separate sibling tree:
  `Math/Analysis.lean`.

  ## Sub-clusters (directory layout)

  Foundation / cut algebra:
    * **`Core/`** — `Real213` type + `Equiv` + `MinimumProposition`,
      `ValidCut`/`ValidCutOps`, `Dyadic`, `AsLensOutput`, `Functions`
    * **`Sum/`** / **`Mul/`** — additive / multiplicative cut algebra
      (`cutSum`, `cutMul`, `cutPow`, `cutInv`, signed cuts, associativity)
    * **`Lattice/`** — `cutPoset` lattice ops (max/min/mid)
    * **`Bisection/`** — bisection algorithm + continuity
    * **`Calculus/`** — cut integration + differentiation-with-modulus
    * **`ExpLog/`** — exp/log/trig cuts, Lambert, Euler, π

  Specific reals / dynamics:
    * **`Phi/`** — golden ratio φ as cut, Fibonacci, Zeckendorf, Pell
    * **`Markov/`** — Markov spectrum, triple, uniqueness, Cassini bridges
    * **`Mobius/`** — Möbius transformations on cuts, Stern–Brocot, setoid
    * **`Minkowski/`** — Minkowski `?`, modular symbols, period polynomials
    * **`ModularGeometry/`** — elliptic / hyperbolic / parabolic traces,
      geodesic lens, holonomy, finite-order spectrum, Lagrange extremes
    * **`Mat2/`** — 2×2 matrix algebra (assoc, Cayley–Hamilton, trace)
    * **`ProbeTwist/`** — probe-twist dynamics + fixed points
    * **`Spiral/`** — spiral coordinate / scaling-orbit invariants

  Approximation / completeness:
    * **`ValidCut/`** — rational instances (½, ⅓, ⅕, ℤ, ℕ) + framework
    * **`CrossDet/`** — cross-determinant overtake / trace-field bounds
    * **`ContinuedFraction/`** — continuant + continued-fraction floor/modulus
    * **`Modulus/`** — convergence-rate moduli (bracket, Liouville, rate)
    * **`Completability/`** — completability grade, intensional/tower completion

  Root-level (foundational / cross-cutting singletons): `AbCutSeq`,
  `ChainToCut`, `NuEscape`, `ObjectIsReadingScaleInvariant`,
  `OracleContinuity`, `PresentationDependence`, `ReciprocalSeries`,
  `CubeRootTwoCut`, `HolonomicReal`, `OdometerSternBrocotUnit`,
  `Zeta3Apery`, `Zeta3Cut`, `FloorReferenceForm`.

  Path = namespace: each module's namespace carries its cluster segment
  (e.g. `…Real213.Phi.PhiCut`).  Cross-cluster references resolve via a
  cluster-parent `open` (e.g. `open …Real213.Mobius`).

  ## Status

  ∅-axiom standard on the production critical path.
-/
