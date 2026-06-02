import E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree
import E213.Lib.Math.CayleyDickson.Integer.ImaginaryQuadraticUnitTrichotomy

/-!
# The spiral axis is the binary half of the crystallographic restriction

Two arcs meet here, both already `∅`-axiom:

  * **`ImaginaryQuadraticUnitTrichotomy`** (analysis side): the spiral-coordinate *axis* —
    the unit-group order of the ring carrying a continued-fraction cross-determinant — is
    exhaustively `{2, 4, 6}` (`imaginary_quadratic_unit_trichotomy`,
    `maximal_order_no_complex_unit`), realised as floor rotations whose midpoint power is the
    central `−1` (`axis_binary_cover`).
  * **`CyclotomicTraceDegree`** (geometry side): the crystallographic restriction — the
    `GL(2,ℤ)`-realisable rotation orders, `φ(n) ≤ 2` — is exactly `{1, 2, 3, 4, 6}`
    (`crystallographic_restriction`).

The bridge is a single decidable identity: the spiral axis `{2,4,6}` is precisely the
**even half** of the crystallographic set `{1,2,3,4,6}`, and that even half is `2·{1,2,3}`
— the central-`−1` doubling.  So the arithmetic unit axis (read off a continued fraction)
and the geometric rotation census (read off `GL(2,ℤ)`) are the same `{1,2,3}` seen through
one binary `2`-fold cover.  This is the `213`-native statement of why the exceptional rungs
are *binary* polyhedral: the `2`-fold cover is the cross-determinant's Cassini sign.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.SpiralAxisCrystallographic

open E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree (phi crystallographic_restriction)

/-- ★★★★ **The spiral axis is the binary half of the crystallographic restriction.**

      1. the crystallographic orders (`φ(n) ≤ 2`) are `{1,2,3,4,6}` (`crystallographic_restriction`);
      2. their **even** members are exactly the spiral axis `{2,4,6}`;
      3. and `{2,4,6} = 2·{1,2,3}` — the central-`−1` (Cassini-sign) binary cover.

    The arithmetic unit-group axis and the geometric `GL(2,ℤ)` rotation census coincide on
    `{1,2,3}`, related by one `2`-fold cover. -/
theorem spiral_axis_is_even_crystallographic :
    ((List.range 13).filter (fun n => 1 ≤ n && phi n ≤ 2) = [1, 2, 3, 4, 6])
    ∧ ([1, 2, 3, 4, 6].filter (fun n => n % 2 == 0) = [2, 4, 6])
    ∧ ([1, 2, 3].map (fun k => 2 * k) = [2, 4, 6]) :=
  ⟨crystallographic_restriction, by decide, by decide⟩

end E213.Lib.Math.CayleyDickson.Tower.SpiralAxisCrystallographic
