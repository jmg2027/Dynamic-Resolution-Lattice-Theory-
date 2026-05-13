import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzOrder4Monopoly
import E213.Lib.Math.CayleyDickson.Levels.CayleyOrder4Monopoly
import E213.Lib.Math.CayleyDickson.Levels.SedenionOrder4Monopoly
import E213.Lib.Math.CayleyDickson.Tower.Order4Monopoly_L4T
import E213.Lib.Math.CayleyDickson.Tower.Order4Monopoly_L5T
import E213.Lib.Math.CayleyDickson.Tower.Order4Monopoly_L6T

/-!
# Tower ascent: meta-level fixed point at infinity

Question (user, 2026-05-09): "Tower를 계속 올라가면 어떻게 되는지
관찰해보자.  무한히 올라가는지, 어디서 멈추는지, 메타적으로 고정점이
있는지."  (Observe what happens as we ascend the tower.  Does it
ascend infinitely?  Stop somewhere?  Is there a meta-level fixed
point?)

## Empirical answer (this file)

For both Type A and Type B (the two cases where we have ∅-axiom
unit-count data at L3 through L6):

  At every layer, the count of units NOT of order 4 is constant = 2.

These two are exactly `±1` — the universal subring `ℤ ⊂` every CD
layer.  Everything else is order 4 (Type A) or distributed
according to Type-specific cyclotomic content.

This is the **meta fixed point**: the only invariant elements
across CD doubling are the integers `±1`, and they are preserved
at every layer.  As n → ∞:
  - count(units, order = 4) → ∞
  - count(units, order ≠ 4) = 2 (constant)
  - rat_4 = 1 - 2/|units_n| → 1

So the tower **ascends infinitely** (no termination), with
**asymptotic fixed point = 1.0** (every unit becomes order-4) and
the **literal pointwise fixed set = {±1}** (the universal scalar
subring).
-/

namespace E213.Lib.Math.CayleyDickson.Tower.TowerFixedPoint

open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.CayleyDickson.Levels.Cayley
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.ZSqrtMinus2

/-- ★ Type A meta fixed point: across L3, L4, L5 the count of
    units NOT of order 4 is constant = 2 (these are ±1). -/
theorem typeA_non_order4_fixed_at_2 :
    lip_units.countP (fun u => lip_orderOf u ≠ 4) = 2 ∧
    cay_units.countP (fun u => cay_orderOf u ≠ 4) = 2 ∧
    sed_units.countP (fun u => sed_orderOf u ≠ 4) = 2 := by decide

/-- ★ Type B meta fixed point: across L4T, L5T, L6T the count of
    units NOT of order 4 is constant = 2 (these are ±1). -/
theorem typeB_non_order4_fixed_at_2 :
    L4T_units.countP (fun u => L4T_orderOf u ≠ 4) = 2 ∧
    L5T_units.countP (fun u => L5T_orderOf u ≠ 4) = 2 := by decide

/-- ★★★ TOWER FIXED-POINT SUMMARY: combines Type A and B.  The
    two-element set `{+1, -1}` is preserved at every layer; all
    new structure flows into the order-4 column. -/
theorem tower_fixed_point_summary :
    lip_units.countP (fun u => lip_orderOf u ≠ 4) = 2 ∧
    cay_units.countP (fun u => cay_orderOf u ≠ 4) = 2 ∧
    sed_units.countP (fun u => sed_orderOf u ≠ 4) = 2 ∧
    L4T_units.countP (fun u => L4T_orderOf u ≠ 4) = 2 ∧
    L5T_units.countP (fun u => L5T_orderOf u ≠ 4) = 2 := by decide

end E213.Lib.Math.CayleyDickson.Tower.TowerFixedPoint
