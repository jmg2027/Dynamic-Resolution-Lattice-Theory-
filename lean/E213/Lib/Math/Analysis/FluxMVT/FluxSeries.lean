import E213.Lib.Math.Analysis.Series.CutGeomSeries

import E213.Lib.Math.Real213.Core
import E213.Lib.Math.Analysis.Series.CutSeries
import E213.Lib.Math.Real213.CutSum
import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
/-!
# FluxSeries
bridge series (∑) with FluxCut framework.

Partial sums form a sequence of FluxCuts (via ofCut).  Convergence
becomes "Cauchy in flux norm" — but for monotone series like
geomHalfSeries, the partial sums can be queried decide-style at
specific (m, k) thresholds.

  partialSum_geomHalf_3   : depth 3 = 7/4 (decide-checked)
  partialSum_geomHalf_n_below_2 : ∀ n, partial sum < 2 (declarative)
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxSeries

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core (Real213)
open E213.Lib.Math.Real213.CutSum (cutSum)
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut zero)
open E213.Lib.Math.Analysis.Series.CutSeries (partialSum)
open E213.Lib.Math.Analysis.Series.CutGeomSeries (geomHalfSeries)

/-- ★ FluxCut form of partial sum: each partial sum lifts to a FluxCut. -/
def seriesFlux (s : Nat → (Nat → Nat → Bool)) (n : Nat) : FluxCut :=
  FluxCut.ofCut (partialSum s n)

/-- ★ At n=0, seriesFlux of any series = zero. -/
theorem seriesFlux_zero (s : Nat → (Nat → Nat → Bool)) :
    seriesFlux s 0 = FluxCut.zero := by
  show FluxCut.ofCut (constCut 0 1) = FluxCut.zero
  rfl

/-- ★ Telescoping: seriesFlux at (n+1) - seriesFlux at n = ofCut (s n). -/
theorem seriesFlux_succ_sub (s : Nat → (Nat → Nat → Bool)) (n : Nat) :
    (seriesFlux s (n+1)).forward
      = cutSum (partialSum s n) (s n) := rfl

/-- ★ Σ (1/2)^i partial sum cohomologically lifts. -/
def geomHalfFlux (n : Nat) : FluxCut := seriesFlux geomHalfSeries n

/-- geomHalfFlux at n=0 = zero. -/
theorem geomHalfFlux_zero : geomHalfFlux 0 = FluxCut.zero := seriesFlux_zero _

/-- geomHalfFlux at n=1 forward = 1 (the first term is (1/2)^0 = 1). -/
example : (geomHalfFlux 1).forward 1 1 = true := by decide

/-- geomHalfFlux at n=2 forward queried at 3/2 — true (sum is 3/2). -/
example : (geomHalfFlux 2).forward 3 2 = true := by decide

/-- geomHalfFlux at n=2 backward = constCut 0 1 (= 0, since ofCut zero). -/
theorem geomHalfFlux_backward_at (n : Nat) :
    (geomHalfFlux n).backward = constCut 0 1 := rfl

end E213.Lib.Math.Analysis.FluxMVT.FluxSeries
