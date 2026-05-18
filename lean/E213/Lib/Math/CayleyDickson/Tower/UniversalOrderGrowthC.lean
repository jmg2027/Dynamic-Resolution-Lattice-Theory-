import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaOct

/-!
# Universal CD doubling order growth — Type C (with cyclotomic preservation)

Type C has additional invariants beyond order-4 growth: cyclotomic
counts (orders 3, 6) PRESERVED across CD doublings.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.UniversalOrderGrowthC

open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaOct

set_option maxHeartbeats 4000000 in
/-- ★ Type C L3 → L4 order-4 growth = +12. -/
theorem typeC_L3_to_L4 :
    zoq_units.countP (fun u => zoq_orderOf u = 4) =
      zod_units.countP (fun u => zod_orderOf u = 4) + zod_units.length := by decide

set_option maxHeartbeats 8000000 in
/-- ★ Type C L4 → L5 order-4 growth = +24. -/
theorem typeC_L4_to_L5 :
    zooct_units.countP (fun u => zooct_orderOf u = 4) =
      zoq_units.countP (fun u => zoq_orderOf u = 4) + zoq_units.length := by decide

/-- ★★ Cyclotomic-3 preserved across all Type C layers. -/
theorem typeC_cyclotomic_3_preserved :
    zod_units.countP (fun u => zod_orderOf u = 3) =
      zoq_units.countP (fun u => zoq_orderOf u = 3) ∧
    zoq_units.countP (fun u => zoq_orderOf u = 3) =
      zooct_units.countP (fun u => zooct_orderOf u = 3) := by decide

set_option maxHeartbeats 4000000 in
/-- ★★ Cyclotomic-6 preserved across all Type C layers. -/
theorem typeC_cyclotomic_6_preserved :
    zod_units.countP (fun u => zod_orderOf u = 6) =
      zoq_units.countP (fun u => zoq_orderOf u = 6) ∧
    zoq_units.countP (fun u => zoq_orderOf u = 6) =
      zooct_units.countP (fun u => zooct_orderOf u = 6) := by decide

/-- ★ Type C units doubling. -/
theorem typeC_units_doubling :
    zoq_units.length = 2 * zod_units.length ∧
    zooct_units.length = 2 * zoq_units.length := by decide

end E213.Lib.Math.CayleyDickson.Tower.UniversalOrderGrowthC
