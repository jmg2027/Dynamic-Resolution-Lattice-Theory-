import E213.Research.HasModulus

/-!
# Research.DiagonalHasModulus: diagonal sequence 의 HasModulus

`abLens.view (xs n) = (n+1, n+1)` (diagonal pair) 의 sequence 가
HasModulus instance.  N(m, k) = 0 (orderProj 가 이미 모든 n
에서 일정).

PellHasModulus 와 함께 second concrete instance — HasModulus
typeclass 의 적용 가능성 demonstration.
-/

namespace E213.Research.DiagonalHasModulus

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS

/-- Diagonal sequence 의 HasModulus instance.  omega 부재. -/
def diagonalHasModulus (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) :
    HasModulus xs where
  N := fun _ _ => 0
  cauchy_at := by
    intro m k _ i j _ _
    rw [h i, h j]
    rw [diagonal_seq_orderProj_const m k (i+1) (Nat.succ_le_succ (Nat.zero_le _)),
        diagonal_seq_orderProj_const m k (j+1) (Nat.succ_le_succ (Nat.zero_le _))]

end E213.Research.DiagonalHasModulus
