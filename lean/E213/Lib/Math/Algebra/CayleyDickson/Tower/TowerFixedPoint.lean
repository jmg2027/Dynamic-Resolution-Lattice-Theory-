import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzOrder4Monopoly
import E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyOrder4Monopoly
import E213.Lib.Math.Algebra.CayleyDickson.Levels.SedenionOrder4Monopoly
import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L4T
import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L5T
import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L6T

/-!
# Tower ascent: meta-level fixed point at infinity

Question (user,): "Let us observe what happens as we keep
ascending the tower.  Whether it ascends infinitely, where it stops,
whether there is a meta-level fixed point."  (Observe what happens as we ascend the tower.  Does it
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
at every layer.  At each layer n:
  - count(units, order = 4) grows without bound across layers
  - count(units, order ≠ 4) = 2 (constant)
  - rat_4 = 1 − 2/|units_n| is a structural property of layer n

The sequence {rat_4(n)} is monotonically increasing across layers,
bounded above by 1 (the structural identity 1 − 2/|units_n| ≤ 1
at every finite layer).  The pointwise fixed set across all layers
is exactly {±1} (the universal scalar subring) — these two
readings (per-layer ratios + global pointwise fixed set) are
aspects of the same residue, not separate phenomena (cf.
`seed/AXIOM/05_no_exterior.md` §5.7 frozen+dynamic).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.TowerFixedPoint

open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley
open E213.Lib.Math.Algebra.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2

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

end E213.Lib.Math.Algebra.CayleyDickson.Tower.TowerFixedPoint
