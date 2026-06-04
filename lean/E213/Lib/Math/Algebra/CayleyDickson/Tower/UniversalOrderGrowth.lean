import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L4T
import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L5T
import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L6T
import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzOrder4Monopoly
import E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyOrder4Monopoly
import E213.Lib.Math.Algebra.CayleyDickson.Levels.SedenionOrder4Monopoly

/-!
# Universal CD doubling order growth law (Type A + B, ∅-axiom)

  order_4_count(L_n) = order_4_count(L_{n-1}) + |units(L_{n-1})|
  |units(L_n)| = 2 × |units(L_{n-1})|

Across all measured Type A and Type B layer pairs.
Type C version in UniversalOrderGrowthC.lean.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.UniversalOrderGrowth

open E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley
open E213.Lib.Math.Algebra.CayleyDickson.Levels.Sedenion

/-- ★ Type B L4 → L5 order-4 growth = +|L4T_units| = +8. -/
theorem typeB_L4_to_L5 :
    L5T_units.countP (fun u => L5T_orderOf u = 4) =
      L4T_units.countP (fun u => L4T_orderOf u = 4) + L4T_units.length := by decide

set_option maxHeartbeats 4000000 in
/-- ★ Type B L5 → L6 order-4 growth = +|L5T_units| = +16. -/
theorem typeB_L5_to_L6 :
    L6T_units.countP (fun u => L6T_orderOf u = 4) =
      L5T_units.countP (fun u => L5T_orderOf u = 4) + L5T_units.length := by decide

/-- ★ Type A L3 → L4 (Lipschitz → Cayley) order-4 growth = +8. -/
theorem typeA_L3_to_L4 :
    cay_units.countP (fun u => cay_orderOf u = 4) =
      lip_units.countP (fun u => lip_orderOf u = 4) + lip_units.length := by decide

set_option maxHeartbeats 4000000 in
/-- ★ Type A L4 → L5 (Cayley → Sedenion) order-4 growth = +16. -/
theorem typeA_L4_to_L5 :
    sed_units.countP (fun u => sed_orderOf u = 4) =
      cay_units.countP (fun u => cay_orderOf u = 4) + cay_units.length := by decide

/-- ★ Total units doubling (Type B). -/
theorem typeB_units_doubling :
    L5T_units.length = 2 * L4T_units.length ∧
    L6T_units.length = 2 * L5T_units.length := by decide

/-- ★ Total units doubling (Type A). -/
theorem typeA_units_doubling :
    cay_units.length = 2 * lip_units.length ∧
    sed_units.length = 2 * cay_units.length := by decide

end E213.Lib.Math.Algebra.CayleyDickson.Tower.UniversalOrderGrowth
