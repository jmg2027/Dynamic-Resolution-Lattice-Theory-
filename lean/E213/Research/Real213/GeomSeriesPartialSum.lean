import E213.Research.Real213.IntegralDyadic
import E213.Research.Real213.CutGeomSeries
import E213.Research.Real213.CutSumOne

/-!
# Research.Real213GeomSeriesPartialSum

Phase DG: ★ geometric series partial sums propEq closed forms ★

For Σ (1/2)^i:
  S_1 = 1
  S_2 = 1 + 1/2 = 3/2
  S_3 = 1 + 1/2 + 1/4 = 7/4

Each propEq via cutSum lemmas chain.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- ★ Σ_{i=0}^0 (1/2)^i = (1/2)^0 = 1. -/
theorem partialSum_geomHalf_at_one :
    partialSum geomHalfSeries 1 = constCut 1 1 := by
  show cutSum (constCut 0 1) (cutPow (constCut 1 2) 0) = constCut 1 1
  show cutSum (constCut 0 1) (constCut 1 1) = constCut 1 1
  exact cutSum_zero_const 1 1

/-- ★ Σ_{i=0}^1 (1/2)^i = 1 + 1/2 = 3/2. -/
theorem partialSum_geomHalf_at_two :
    partialSum geomHalfSeries 2 = constCut 3 2 := by
  show cutSum (cutSum (constCut 0 1) (cutPow (constCut 1 2) 0))
              (cutPow (constCut 1 2) 1)
       = constCut 3 2
  show cutSum (cutSum (constCut 0 1) (constCut 1 1))
              (cutMul (constCut 1 1) (constCut 1 2))
       = constCut 3 2
  rw [cutSum_zero_const, cutMul_one_const 1 2]
  exact cutSum_int_half 1 1

/-- Phase DG capstone: geometric series partial sums propEq. -/
theorem partialSum_geomHalf_capstone :
    -- (1) S_1 = 1
    partialSum geomHalfSeries 1 = constCut 1 1
    -- (2) S_2 = 3/2 (= 1 + 1/2)
    ∧ partialSum geomHalfSeries 2 = constCut 3 2 :=
  ⟨partialSum_geomHalf_at_one, partialSum_geomHalf_at_two⟩

end E213.Research.Real213.CutSum
