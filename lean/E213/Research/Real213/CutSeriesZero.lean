import E213.Research.Real213.CutSeries
import E213.Research.Real213.CutSumZero

/-!
# Research.Real213CutSeriesZero: partialSum of zero series = zero

Σ_{i<n} 0 = 0 at cut level.
-/

namespace E213.Research.Real213.CutSeriesZero

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

/-- **zero series is a SeriesCauchy instance** (concrete instance). -/
def zeroSeriesCauchy : SeriesCauchy where
  terms := fun _ => constCut 0 1
  N := fun _ _ => 0
  cauchy := by
    intro m k i j _ _
    rw [partialSum_zero_series, partialSum_zero_series]

/-- limit of zero series = 0. -/
theorem zeroSeriesCauchy_limit : zeroSeriesCauchy.limit = constCut 0 1 := by
  funext m k
  show partialSum _ 0 m k = constCut 0 1 m k
  rfl

end E213.Research.Real213.CutSeriesZero
