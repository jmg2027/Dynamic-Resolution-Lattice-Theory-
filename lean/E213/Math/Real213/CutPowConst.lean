import E213.Math.Real213.CutPow
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutSumZero
import E213.Math.Real213.CutMulDetermined

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumTest
/-!
# CutPowConst: cutPow on const cuts

cutPow (constCut a b) 0 = 1, cutPow (constCut a b) 1 = (constCut a b).
-/

namespace E213.Math.Real213.CutPowConst

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul cutMulOuter)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)

-- DELETED: function-eq cutPow_one_const. Use cutPow_one_const_at.

/-- (a/b)^1 = a/b pointwise (∅-axiom). -/
theorem cutPow_one_const_at (a b m k : Nat) :
    cutPow (constCut a b) 1 m k = constCut a b m k :=
  cutMul_one_const_at a b m k

/-- **0^(n+1) = 0** pointwise (∅-axiom).  Uses `cutMulOuter_congr`
    instead of `funext` for the inductive step. -/
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
    -- Use cutMulOuter_congr to swap cutPow (constCut 0 1) (j+1) → constCut 0 1
    -- pointwise (no funext).
    show cutMulOuter (cutPow (constCut 0 1) (j+1)) (constCut 0 1)
                     k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
    have step :
        cutMulOuter (cutPow (constCut 0 1) (j+1)) (constCut 0 1)
                    k m ((m+1)*(k+1)) ((m+1)*(k+1))
        = cutMulOuter (constCut 0 1) (constCut 0 1)
                    k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
      cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
        (cutPow (constCut 0 1) (j+1)) (constCut 0 1)
        (constCut 0 1) (constCut 0 1)
        (fun m' _ => cutPow_zero_succ_at j m' k)
        (fun _ _ => rfl)
        ((m+1)*(k+1)) (Nat.le_refl _)
    rw [step]
    exact cutMul_zero_zero_at m k

-- DELETED: function-eq cutPow_zero_succ. Use cutPow_zero_succ_at.

/-- **1^n = 1** pointwise (∅-axiom).  Uses `cutMulOuter_congr`. -/
theorem cutPow_one_n_at :
    ∀ (n m k : Nat), cutPow (constCut 1 1) n m k = constCut 1 1 m k
  | 0, _, _ => rfl
  | j+1, m, k => by
    show cutMul (cutPow (constCut 1 1) j) (constCut 1 1) m k
        = constCut 1 1 m k
    show cutMulOuter (cutPow (constCut 1 1) j) (constCut 1 1)
                     k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
    have step :
        cutMulOuter (cutPow (constCut 1 1) j) (constCut 1 1)
                    k m ((m+1)*(k+1)) ((m+1)*(k+1))
        = cutMulOuter (constCut 1 1) (constCut 1 1)
                    k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
      cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
        (cutPow (constCut 1 1) j) (constCut 1 1)
        (constCut 1 1) (constCut 1 1)
        (fun m' _ => cutPow_one_n_at j m' k)
        (fun _ _ => rfl)
        ((m+1)*(k+1)) (Nat.le_refl _)
    rw [step]
    exact cutMul_one_one_at m k

-- DELETED: function-eq cutPow_one_n. Use cutPow_one_n_at.

end E213.Math.Real213.CutPowConst
