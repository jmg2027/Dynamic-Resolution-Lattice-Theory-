import E213.Lib.Math.Real213.AsLensOutput
import E213.Lib.Math.Real213.ConstCutScale
import E213.Lib.Math.Real213.Core
import E213.Lib.Math.Real213.CutAlgebraStruct
import E213.Lib.Math.Real213.CutAlgebraic
import E213.Lib.Math.Real213.CutBinary
import E213.Lib.Math.Real213.CutBisection
import E213.Lib.Math.Real213.CutBisectionAlgo
import E213.Lib.Math.Real213.CutContinuity
import E213.Lib.Math.Real213.CutDistance
import E213.Lib.Math.Real213.CutDouble
import E213.Lib.Math.Real213.CutFnData
import E213.Lib.Math.Real213.CutInv
import E213.Lib.Math.Real213.CutLatticeEq
import E213.Lib.Math.Real213.CutMaxMin
import E213.Lib.Math.Real213.CutMidMono
import E213.Lib.Math.Real213.CutMidSelf
import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Real213.CutMulComm
import E213.Lib.Math.Real213.CutMulConstConst
import E213.Lib.Math.Real213.CutMulDetermined
import E213.Lib.Math.Real213.CutMulOne
import E213.Lib.Math.Real213.CutMulTest
import E213.Lib.Math.Real213.CutPoly
import E213.Lib.Math.Real213.CutPoset
import E213.Lib.Math.Real213.CutPow
import E213.Lib.Math.Real213.CutPowConst
import E213.Lib.Math.Real213.CutScaleLattice
import E213.Lib.Math.Real213.CutSum
import E213.Lib.Math.Real213.CutSumComm
import E213.Lib.Math.Real213.CutSumDetermined
import E213.Lib.Math.Real213.CutSumEq
import E213.Lib.Math.Real213.CutSumGeneral
import E213.Lib.Math.Real213.CutSumOne
import E213.Lib.Math.Real213.CutSumPointwise
import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Real213.CutSumZero
import E213.Lib.Math.Real213.Dyadic
import E213.Lib.Math.Real213.Equiv
import E213.Lib.Math.Real213.Functions
import E213.Lib.Math.Real213.MinimumProposition
import E213.Lib.Math.Real213.Signed
import E213.Lib.Math.Real213.SignedSum
import E213.Lib.Math.Real213.ValidCut
import E213.Lib.Math.Real213.ValidCutOps

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
