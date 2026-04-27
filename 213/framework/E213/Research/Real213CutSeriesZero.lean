import E213.Research.Real213CutSeries
import E213.Research.Real213CutSumZero

/-!
# Research.Real213CutSeriesZero: partialSum of zero series = zero

Σ_{i<n} 0 = 0 at cut level.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- partialSum of zero series = zero (at any n). -/
theorem partialSum_zero_series (n : Nat) :
    partialSum (fun _ => constCut 0 1) n = constCut 0 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show cutSum (partialSum (fun _ => constCut 0 1) k) (constCut 0 1)
       = constCut 0 1
    rw [ih, cutSum_zero_zero]

end E213.Research.Real213CutSum
