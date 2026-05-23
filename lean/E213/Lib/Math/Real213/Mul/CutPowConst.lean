import E213.Lib.Math.Real213.Mul.CutPow
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Lib.Math.Real213.Sum.CutSumZero
import E213.Lib.Math.Real213.Mul.CutMulDetermined
import E213.Lib.Math.Real213.Mul.CutMulOuterReduce

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# CutPowConst: cutPow on const cuts

cutPow (constCut a b) 0 = 1, cutPow (constCut a b) 1 = (constCut a b).
-/

namespace E213.Lib.Math.Real213.Mul.CutPowConst

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutPow (cutPow)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Mul.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Lib.Math.Real213.Sum.CutSumZero (cutMul_zero_zero_at)
open E213.Lib.Math.Real213.Mul.CutMulDetermined (cutMulOuter_congr)
open E213.Lib.Math.Real213.Mul.CutMulOuterReduce (cutMulOuter_reduce_at)

-- DELETED: function-eq cutPow_one_const. Use cutPow_one_const_at.

/-- (a/b)^1 = a/b pointwise (∅-axiom). -/
theorem cutPow_one_const_at (a b m k : Nat) :
    cutPow (constCut a b) 1 m k = constCut a b m k :=
  cutMul_one_const_at a b m k

/-- **0^(n+1) = 0** pointwise (∅-axiom).  Uses `cutMulOuter_reduce_at`
    template (FLUX-1, upstream variant) for the inductive step. -/
theorem cutPow_zero_succ_at :
    ∀ (n m k : Nat), cutPow (constCut 0 1) (n+1) m k = constCut 0 1 m k
  | 0, m, k => by
    show cutMul (cutPow (constCut 0 1) 0) (constCut 0 1) m k
        = constCut 0 1 m k
    show cutMul (constCut 1 1) (constCut 0 1) m k = constCut 0 1 m k
    exact cutMul_one_const_at 0 1 m k
  | j+1, m, k => by
    show cutMul (cutPow (constCut 0 1) (j+1)) (constCut 0 1) m k
        = constCut 0 1 m k
    show cutMulOuter (cutPow (constCut 0 1) (j+1)) (constCut 0 1)
                     k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
    rw [cutMulOuter_reduce_at
          (cutPow (constCut 0 1) (j+1)) (constCut 0 1)
          (constCut 0 1) (constCut 0 1) m k ((m+1)*(k+1))
          (fun m' _ => cutPow_zero_succ_at j m' k) (fun _ _ => rfl)]
    exact cutMul_zero_zero_at m k

-- DELETED: function-eq cutPow_zero_succ. Use cutPow_zero_succ_at.

/-- **1^n = 1** pointwise (∅-axiom).  Uses `cutMulOuter_reduce_at`
    template (FLUX-1, upstream variant). -/
theorem cutPow_one_n_at :
    ∀ (n m k : Nat), cutPow (constCut 1 1) n m k = constCut 1 1 m k
  | 0, _, _ => rfl
  | j+1, m, k => by
    show cutMul (cutPow (constCut 1 1) j) (constCut 1 1) m k
        = constCut 1 1 m k
    show cutMulOuter (cutPow (constCut 1 1) j) (constCut 1 1)
                     k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
    rw [cutMulOuter_reduce_at
          (cutPow (constCut 1 1) j) (constCut 1 1)
          (constCut 1 1) (constCut 1 1) m k ((m+1)*(k+1))
          (fun m' _ => cutPow_one_n_at j m' k) (fun _ _ => rfl)]
    exact cutMul_one_one_at m k

-- DELETED: function-eq cutPow_one_n. Use cutPow_one_n_at.

end E213.Lib.Math.Real213.Mul.CutPowConst
