import E213.Research.Real213CutSeries
import E213.Research.Real213CutSumOne

/-!
# Research.Real213CutSeriesConst: partial sums of constant series

partialSum (fun _ => c) n at small n via verified cutSum identities.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- partialSum of constant a/b at n = 1 = a/b. -/
theorem partialSum_const_one (a b : Nat) :
    partialSum (fun _ => constCut a b) 1 = constCut a b := by
  show cutSum (constCut 0 1) (constCut a b) = constCut a b
  exact cutSum_zero_const a b

/-- partialSum of constant a/b at n = 2 = (2a)/b. -/
theorem partialSum_const_two (a b : Nat) :
    partialSum (fun _ => constCut a b) 2 = constCut (2*a) b := by
  show cutSum (partialSum (fun _ => constCut a b) 1) (constCut a b)
       = constCut (2*a) b
  rw [partialSum_const_one]
  exact cutSum_self a b

/-- partialSum of constant a/1 at n = 3 = 3a/1 (integers). -/
theorem partialSum_const_three_int (a : Nat) :
    partialSum (fun _ => constCut a 1) 3 = constCut (3*a) 1 := by
  show cutSum (partialSum (fun _ => constCut a 1) 2) (constCut a 1)
       = constCut (3*a) 1
  rw [partialSum_const_two]
  have h := cutSum_int_int (2*a) a
  rw [show (2*a + a) = 3*a from by omega] at h
  exact h

/-- partialSum of constant a/2 at n = 3 = 3a/2 (halves). -/
theorem partialSum_const_three_half (a : Nat) :
    partialSum (fun _ => constCut a 2) 3 = constCut (3*a) 2 := by
  show cutSum (partialSum (fun _ => constCut a 2) 2) (constCut a 2)
       = constCut (3*a) 2
  rw [partialSum_const_two]
  have h := cutSum_half_general (2*a) a
  rw [show (2*a + a) = 3*a from by omega] at h
  exact h

/-- **partialSum of integer constant a/1 at any n = (n*a)/1**.
    Holds for all n ≥ 0 because constCut 0 1 matches the n=0 case. -/
theorem partialSum_const_int (a : Nat) :
    ∀ n, partialSum (fun _ => constCut a 1) n = constCut (n*a) 1
  | 0 => by
    show constCut 0 1 = constCut (0*a) 1
    rw [Nat.zero_mul]
  | n+1 => by
    show cutSum (partialSum (fun _ => constCut a 1) n) (constCut a 1)
         = constCut ((n+1)*a) 1
    rw [partialSum_const_int a n]
    have h := cutSum_int_int (n*a) a
    rw [(Nat.succ_mul n a).symm] at h
    exact h

/-- **partialSum of half constant a/2 at any n ≥ 1 = (n*a)/2**.
    Stated from n+1 to avoid the n=0 edge case where the partialSum
    base constCut 0 1 differs from constCut 0 2 at the function level
    (they are cut-equal but not function-equal). -/
theorem partialSum_const_half (a : Nat) :
    ∀ n, partialSum (fun _ => constCut a 2) (n+1) = constCut ((n+1)*a) 2
  | 0 => by
    show cutSum (constCut 0 1) (constCut a 2) = constCut (1*a) 2
    rw [cutSum_zero_const, Nat.one_mul]
  | n+1 => by
    show cutSum (partialSum (fun _ => constCut a 2) (n+1)) (constCut a 2)
         = constCut ((n+2)*a) 2
    rw [partialSum_const_half a n]
    have h := cutSum_half_general ((n+1)*a) a
    rw [(Nat.succ_mul (n+1) a).symm] at h
    exact h

end E213.Research.Real213CutSum
