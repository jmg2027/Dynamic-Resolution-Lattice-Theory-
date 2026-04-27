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

end E213.Research.Real213CutSum
