import E213.Research.Real213CutPow
import E213.Research.Real213CutSeries

/-!
# Research.Real213CutGeomSeries: geometric series + concrete examples

(1/2)^i geometric series — partial sums computable.

Σ_{i=0}^∞ (1/2)^i = 2 (limit, declarative).
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- (1/2)^i geometric series. -/
def geomHalfSeries : Nat → (Nat → Nat → Bool) :=
  fun i => cutPow (constCut 1 2) i

/-- Partial sum of (1/2)^i at n = 0 = 0 (empty sum). -/
example : partialSum geomHalfSeries 0 = constCut 0 1 := rfl

/-- Partial sum n=1 = 1 (just the first term (1/2)^0 = 1). -/
example : partialSum geomHalfSeries 1 1 1 = true := by decide

/-- Partial sum n=1 = 1, NOT ≤ 0/1. -/
example : partialSum geomHalfSeries 1 0 1 = false := by decide

end E213.Research.Real213CutSum
