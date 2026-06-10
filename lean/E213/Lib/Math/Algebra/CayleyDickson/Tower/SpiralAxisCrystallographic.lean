import E213.Lib.Math.Algebra.CayleyDickson.Tower.CyclotomicTraceDegree
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ImaginaryQuadraticUnitTrichotomy

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

The file also closes the **defensive** companion fact (`cd_tower_axis_noncoincidence`): the
Cayley–Dickson dimension tower `{1,2,4,8} = 2ⁿ` is *not* the spiral axis `{2,4,6}` — they meet
only on `{2,4}` and diverge for two independent reasons (`8 = 2³` is a power of two but not a
crystallographic order, `φ 8 = 4 > 2`; `6` is a crystallographic order but no power of two).
So the axis's Cayley–Dickson content flows through the *rings* `ℤ[i], ℤ[ω]`, not the dimension
doubling — a stereotype-match (`1,2,4,8 ↔ {2,4,6}`) ruled out, not asserted.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.SpiralAxisCrystallographic

open E213.Lib.Math.Algebra.CayleyDickson.Tower.CyclotomicTraceDegree (phi crystallographic_restriction)

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

/-! ## The CD-dimension tower is *not* the spiral axis (non-coincidence) -/

/-- No power of `2` equals `6`: `6 = 2·3` carries the odd prime `3`, which the powers-of-two
    tower never reaches (it jumps `4 = 2² → 8 = 2³`). -/
theorem not_pow_two_six : ∀ k, (2 : Nat) ^ k ≠ 6
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | k + 3 => fun h => by
      have hle : (2 : Nat) ^ 3 ≤ 2 ^ (k + 3) :=
        Nat.pow_le_pow_right (by decide) (Nat.le_add_left 3 k)
      rw [h] at hle
      exact absurd hle (by decide)

/-- ★★★ **The Cayley–Dickson dimension tower `{1,2,4,8}` is not the spiral axis `{2,4,6}`.**
    The tempting `1,2,4,8 ↔ {2,4,6}` map is a stereotype: the two sequences coincide only on
    `{2,4}` and then diverge for two independent structural reasons —

      1. the octonion dimension `8 = 2³` is a power of two but **not a crystallographic order**
         (`φ 8 = 4 > 2`), so it has no spiral-axis (rotation-order) reading — *no octonion at the
         axis*;
      2. the Eisenstein axis order `6` is crystallographic (`φ 6 = 2`) but **not a power of two**
         (`not_pow_two_six`), so it is no Cayley–Dickson dimension — *no order-6 rung in the CD
         tower*.

    The real Cayley–Dickson content of the axis flows through the *rings* `ℤ[i], ℤ[ω]` (unit
    orders `4, 6`), not the dimension doubling `2ⁿ`. -/
theorem cd_tower_axis_noncoincidence :
    -- the CD dims `2ⁿ` (n ≤ 3) meet the axis `{2,4,6}` only on `{2,4}`
    (([1, 2, 4, 8].filter (fun m => m == 2 || m == 4 || m == 6)) = [2, 4])
    -- reason 1: `8 = 2³` is in the CD tower but **not crystallographic** (`φ 8 = 4 > 2`); since
    --   the axis is the even half of the crystallographic set, `8` is off the axis.
    ∧ ((2 : Nat) ^ 3 = 8 ∧ phi 8 = 4 ∧ ¬ phi 8 ≤ 2)
    -- reason 2: `6` is crystallographic (`φ 6 = 2`, hence on the even-crystallographic axis)
    --   but no power of two (`not_pow_two_six`), so it is no Cayley–Dickson dimension.
    ∧ (phi 6 = 2 ∧ ∀ k, (2 : Nat) ^ k ≠ 6) :=
  ⟨by decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, not_pow_two_six⟩⟩

end E213.Lib.Math.Algebra.CayleyDickson.Tower.SpiralAxisCrystallographic
