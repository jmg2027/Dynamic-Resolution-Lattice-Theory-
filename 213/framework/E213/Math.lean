import E213.Research.Real213
import E213.Research.Real213Equiv
import E213.Research.Real213Const
import E213.Research.Real213Order
import E213.Research.Real213OrderExtra
import E213.Research.Real213Sign
import E213.Research.Real213CutSum
import E213.Research.Real213CutSumTest
import E213.Research.Real213CutMul
import E213.Research.Real213CutMulTest
import E213.Research.Real213CutMaxMin
import E213.Research.Real213CutAlgebraic
import E213.Research.Real213CauchyComplete
import E213.Research.Real213CutContinuity
import E213.Research.Real213CutSumDetermined
import E213.Research.Real213CutMulDetermined
import E213.Research.Real213CutFnData
import E213.Research.Real213CutBinary
import E213.Research.Real213CutBinaryOp
import E213.Research.Real213CutBinaryInstances
import E213.Research.Real213CutDistance
import E213.Research.Real213CutSequence
import E213.Research.Real213CutBisection
import E213.Research.Real213CutSeries
import E213.Research.Real213Signed
import E213.Research.Real213SignedSum
import E213.Research.Real213CutInv
import E213.Research.Real213CutAlgebraStruct
import E213.Research.Real213CutPow
import E213.Research.Real213CutPoly
import E213.Research.Real213CutGeomSeries
import E213.Research.Real213CutExp
import E213.Research.Real213CutPoset
import E213.Research.Real213AsLensOutput
import E213.Research.Real213RecurrenceLens
import E213.Research.Real213CutTrig

/-!
# E213.Math: 213-native real analysis library (root entry)

라이브러리화 entry point — stable cut-level real analysis foundation.

## Structure

- **Real213**: framework-internal Cauchy ℝ type.
- **Order/Sign**: le, lt, positive.
- **Cut operations**: cutSum, cutMul, cutMax, cutMin, cutInv, cutNeg.
- **Generic kernel**: cutBinary + CutBinaryOp.
- **Continuity**: locally-determined + composition.
- **Cauchy completeness**: Real-valued sequence + limit.
- **Series**: partialSum + SeriesCauchy.
- **Bisection**: cutHalf, cutMid (IVT support).
- **Distance**: cutAbs + cutDistance.

## Status

이 모듈 의 imports 가 모두 build 통과 + 0 sorry + ≤ propext +
Quot.sound (Lean 4 core 만).

연 구 단 계 (incomplete proofs, scaffolding) 는 `Research/` 안 의 별 도
modules — `Real213StrictPos`, `StrongModulus`, `Real213ModulusCombiner`,
`Real213IVT`, `Real213Diff`, `Real213Integration`, `Real213Functions` 등.
-/
