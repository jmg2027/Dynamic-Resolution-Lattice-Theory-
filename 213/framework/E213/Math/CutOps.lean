import E213.Research.Real213CutSum
import E213.Research.Real213CutSumTest
import E213.Research.Real213CutMul
import E213.Research.Real213CutMulTest
import E213.Research.Real213CutMaxMin
import E213.Research.Real213CutAlgebraic
import E213.Research.Real213CutDistance
import E213.Research.Real213CutBisection
import E213.Research.Real213CutPow
import E213.Research.Real213CutPoly
import E213.Research.Real213CutInv
import E213.Research.Real213Signed
import E213.Research.Real213SignedSum
import E213.Research.Real213CutAlgebraStruct
import E213.Research.Real213CutPoset
import E213.Research.Real213CutSumComm
import E213.Research.Real213CutMulComm
import E213.Research.Real213CutSumZero
import E213.Research.Real213CutSumEq
import E213.Research.Real213CutDouble
import E213.Research.Real213CutMoreTests

/-!
# E213.Math.CutOps: cut-level rational arithmetic operations

cutSum / cutMul / cutMaxMin / cutNeg / cutSignedMul / cutInv / cutDiv /
cutAbs / cutDistance / cutHalf / cutMid / cutPow / cutScale / evalPoly /
SignedCut / cutSignedSum / cutSignedSub.

Algebraic properties: cutMax/Min idempotent, lattice ops.
Cut poset: cutEq, cutLe, antisymm.
CutAlgebra struct: stdCutAlgebra.

## Library status: STABLE

대부분 0 axioms or ≤ propext + Quot.sound (funext).
-/
