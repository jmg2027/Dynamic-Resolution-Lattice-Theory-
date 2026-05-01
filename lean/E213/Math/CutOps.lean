import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulTest
import E213.Math.Real213.CutMaxMin
import E213.Math.Real213.CutAlgebraic
import E213.Math.Real213.CutDistance
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutPoly
import E213.Math.Real213.CutInv
import E213.Math.Real213.Signed
import E213.Math.Real213.SignedSum
import E213.Math.Real213.CutAlgebraStruct
import E213.Math.Real213.CutPoset
import E213.Math.Real213.CutSumComm
import E213.Math.Real213.CutMulComm
import E213.Math.Real213.CutSumZero
import E213.Math.Real213.CutSumEq
import E213.Math.Real213.CutDouble
import E213.Math.Real213.CutMoreTests
import E213.Math.Real213.CutScaleLattice
import E213.Math.Real213.CutLatticeEq
import E213.Math.Real213.SignedMulConst
import E213.Math.Real213.CutMidEq
import E213.Math.Real213.CutSumOne
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutMidSelf
import E213.Math.Real213.CutPowConst
import E213.Math.Real213.ConstCutScale

/-!
# E213.Math.CutOps: cut-level rational arithmetic operations

cutSum / cutMul / cutMaxMin / cutNeg / cutSignedMul / cutInv / cutDiv /
cutAbs / cutDistance / cutHalf / cutMid / cutPow / cutScale / evalPoly /
SignedCut / cutSignedSum / cutSignedSub.

Algebraic properties: cutMax/Min idempotent, lattice ops.
Cut poset: cutEq, cutLe, antisymm.
CutAlgebra struct: stdCutAlgebra.

## Library status: STABLE

Mostly 0 axioms or ≤ propext + Quot.sound (funext).
-/
