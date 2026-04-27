import E213.Research.Real213CutSumComm
import E213.Research.Real213CutMulComm
import E213.Research.Real213CutAlgebraic

/-!
# Research.Real213CutSumZero: cutSum (zero) (zero) = zero

Specific algebraic identity: 0 + 0 = 0 at cut level.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **cutSum 0 0 = 0** at cut level. -/
theorem cutSum_zero_zero : cutSum (constCut 0 1) (constCut 0 1) = constCut 0 1 := by
  funext m k
  show cutSum (constCut 0 1) (constCut 0 1) m k = constCut 0 1 m k
  rw [constCut_zero_always]
  show cutSumAux (constCut 0 1) (constCut 0 1) k (2*m) (2*m) = true
  rw [cutSumAux_eq_true_iff]
  exact ⟨0, Nat.zero_le _,
         constCut_zero_always 0 (2*k),
         constCut_zero_always (2*m - 0) (2*k)⟩

/-- **cutMul 0 0 = 0**: 0 * 0 = 0. -/
theorem cutMul_zero_zero : cutMul (constCut 0 1) (constCut 0 1) = constCut 0 1 := by
  funext m k
  show cutMul (constCut 0 1) (constCut 0 1) m k = constCut 0 1 m k
  rw [constCut_zero_always]
  show cutMulOuter (constCut 0 1) (constCut 0 1) k m ((m+1)*(k+1)) ((m+1)*(k+1))
       = true
  rw [cutMulOuter_eq_true_iff]
  refine ⟨0, Nat.zero_le _, 0, Nat.zero_le _, ?_, ?_, ?_⟩
  · exact constCut_zero_always 0 k
  · exact constCut_zero_always 0 k
  · rw [Nat.zero_mul]; exact Nat.zero_le _

end E213.Research.Real213CutSum
