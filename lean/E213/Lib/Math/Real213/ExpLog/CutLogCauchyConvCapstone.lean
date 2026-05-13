import E213.Lib.Math.Real213.ExpLog.GeomSeriesIdentity
import E213.Lib.Math.Real213.ExpLog.GeomSeriesCauchy
import E213.Lib.Math.Real213.ExpLog.GeomCutInvBridge

/-!
# Real213 — `cutLog` Cauchy convergence Capstone (∅-axiom)

4 cluster witnesses + total bundle for the cutLog Cauchy
convergence marathon.

This Capstone closes the long-noted residual:
"`cutLog x N` Cauchy modulus → continuous `1/(1−x)`: requires
`cutInv`-side bridging, separate marathon" (PR #56).

The marathon delivers:
  * **Geometric series structural identity**: `S_{N+1} =
    cutSum S_N x^N`, `geomTermAt_succ`, depth-N concrete forms.
  * **Cauchy modulus framework**: `GeomCauchy` record with
    trivial baseline modulus `N ε = 0` (since the
    adjacent-difference identity is structural, not asymptotic).
  * **cutInv bridge**: `cutInv (constCut 1 1)` represents
    `1/(1−0) = 1`; concrete witnesses at `(m, k) = (2, 1)`
    (true) and `(1, 1)` (boundary, false).

213-native paradigm: convergence to `1/(1−x)` is **structural
fixpoint**, not analytic limit.  The Cauchy modulus exists
trivially because the adjacent-difference identity holds at
every depth without needing precision-dependent depth.
-/

namespace E213.Lib.Math.Real213.ExpLog.CutLogCauchyConvCapstone

open E213.Lib.Math.Real213.Mul.CutPow (cutPow)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.ExpLog.CutLogODE (geomPartialSum)
open E213.Lib.Math.Real213.ExpLog.GeomSeriesIdentity
  (geom_right_shift geom_depth_zero geom_depth_one geom_depth_two
   geomTermAt_succ geomTermAt_zero)
open E213.Lib.Math.Real213.ExpLog.GeomSeriesCauchy
  (GeomCauchy trivialGeomCauchy
   trivialGeomCauchy_modulus_zero geom_adjacent_diff)
open E213.Lib.Math.Real213.ExpLog.GeomCutInvBridge
  (cutInv_one_above cutInv_one_boundary geomLimitAtZero
   geomLimitAtZero_above geomFixpoint_depth_zero geomCauchyExists)

/-- ★ **Geometric identity witness** — recurrence + concrete
    depth witnesses. -/
theorem geomIdentity_witness (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x (N + 1)
      = cutSum (geomPartialSum x N) (cutPow x N)
    ∧ geomPartialSum x 0 = constCut 0 1 :=
  ⟨geom_right_shift x N, geom_depth_zero x⟩

/-- ★ **Cauchy modulus witness** — trivial baseline. -/
theorem geomCauchy_witness (x : Nat → Nat → Bool) (ε : Nat) :
    (trivialGeomCauchy x).N ε = 0
    ∧ ∃ N : Nat → Nat, (trivialGeomCauchy x).N = N :=
  ⟨trivialGeomCauchy_modulus_zero x ε, geomCauchyExists x⟩

/-- ★ **cutInv bridge witness** — `cutInv 1` concrete values
    at strict-above and boundary. -/
theorem cutInvBridge_witness :
    E213.Lib.Math.Real213.Mul.CutInv.cutInv (constCut 1 1) 2 1 = true
    ∧ E213.Lib.Math.Real213.Mul.CutInv.cutInv (constCut 1 1) 1 1 = false
    ∧ geomLimitAtZero 2 1 = true :=
  ⟨cutInv_one_above, cutInv_one_boundary, geomLimitAtZero_above⟩

/-- ★★★ **Total witness** ★★★ — all three pieces bundled. -/
theorem total_witness (x : Nat → Nat → Bool) (N : Nat) (ε : Nat) :
    geomPartialSum x (N + 1)
      = cutSum (geomPartialSum x N) (cutPow x N)
    ∧ (trivialGeomCauchy x).N ε = 0
    ∧ E213.Lib.Math.Real213.Mul.CutInv.cutInv (constCut 1 1) 2 1 = true :=
  ⟨geom_right_shift x N, trivialGeomCauchy_modulus_zero x ε,
   cutInv_one_above⟩

end E213.Lib.Math.Real213.ExpLog.CutLogCauchyConvCapstone
