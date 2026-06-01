import E213.Lib.Math.Real213.Core.AsLensOutput
import E213.Lib.Math.Real213.Mul.ConstCutScale
import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Core.CutAlgebraStruct
import E213.Lib.Math.Real213.Mul.CutAlgebraic
import E213.Lib.Math.Real213.Mul.CutBinary
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Bisection.CutBisectionAlgo
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Mul.CutDistance
import E213.Lib.Math.Real213.Mul.CutDouble
import E213.Lib.Math.Real213.Core.CutFnData
import E213.Lib.Math.Real213.Mul.CutInv
import E213.Lib.Math.Real213.Lattice.CutLatticeEq
import E213.Lib.Math.Real213.Lattice.CutMaxMin
import E213.Lib.Math.Real213.Lattice.CutMidMono
import E213.Lib.Math.Real213.Lattice.CutMidSelf
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutMulComm
import E213.Lib.Math.Real213.Mul.CutMulConstConst
import E213.Lib.Math.Real213.Mul.CutMulDetermined
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Lib.Math.Real213.Mul.CutMulTest
import E213.Lib.Math.Real213.Mul.CutPoly
import E213.Lib.Math.Real213.Core.CutPoset
import E213.Lib.Math.Real213.Mul.CutPow
import E213.Lib.Math.Real213.Mul.CutPowConst
import E213.Lib.Math.Real213.Lattice.CutScaleLattice
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumComm
import E213.Lib.Math.Real213.Sum.CutSumDetermined
import E213.Lib.Math.Real213.Sum.CutSumEq
import E213.Lib.Math.Real213.Sum.CutSumGeneral
import E213.Lib.Math.Real213.Sum.CutSumOne
import E213.Lib.Math.Real213.Sum.CutSumPointwise
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Real213.Sum.CutSumZero
import E213.Lib.Math.Real213.Core.Dyadic
import E213.Lib.Math.Real213.Core.Equiv
import E213.Lib.Math.Real213.Core.Functions
import E213.Lib.Math.Real213.Core.MinimumProposition
import E213.Lib.Math.Real213.Sum.Signed
import E213.Lib.Math.Real213.Sum.SignedSum
import E213.Lib.Math.Real213.Core.ValidCut
import E213.Lib.Math.Real213.Core.ValidCutOps
import E213.Lib.Math.Real213.ChainToCut
import E213.Lib.Math.Real213.ObjectIsReadingScaleInvariant
import E213.Lib.Math.Real213.PhiConvergence
import E213.Lib.Math.Real213.PhiAsCut
import E213.Lib.Math.Real213.PhiCutConvergents
import E213.Lib.Math.Real213.PhiNormInvariant
import E213.Lib.Math.Real213.FibCassiniNat
import E213.Lib.Math.Real213.PhiCauchyLimit
import E213.Lib.Math.Real213.HolonomicReal
import E213.Lib.Math.Real213.RateModulus
import E213.Lib.Math.Real213.CrossDetOvertake
import E213.Lib.Math.Real213.LiouvilleModulus
import E213.Lib.Math.Real213.CrossDetEqDenom
import E213.Lib.Math.Real213.ReciprocalSeries
import E213.Lib.Math.Real213.CrossDetConstDenom
import E213.Lib.Math.Real213.GeometricThreshold
import E213.Lib.Math.Real213.PresentationDependence
import E213.Lib.Math.Real213.TowerNativeCompleteness
import E213.Lib.Math.Real213.ExpLog.EulerCertifiedBracket
import E213.Lib.Math.Real213.ExpLog.EulerModulus

/-! Spec-as-code entry point for `E213.Lib.Math.Real213`.

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
