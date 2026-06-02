import E213.Lib.Math.CayleyDickson.Integer.ZIUnits
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaUnits

/-!
# The imaginary-quadratic unit trichotomy — the spiral axis is exhaustive

The spiral-coordinate **axis** is the unit-group order of the integer ring carrying a
continued-fraction cross-determinant.  `ZIUnits` and `ZOmegaUnits` build the two
non-trivial axes — `|ℤ[i]^×| = 4` and `|ℤ[ω]^×| = 6` — as exact-cardinality theorems.
This file closes the **exhaustiveness**: there is *no fourth axis*.

The classical statement (Dirichlet's unit theorem for imaginary-quadratic orders, "cited
not formalized" in `Tower/SeedUnitGovernance`) is that `ℤ[i]` and `ℤ[ω]` are the *only*
imaginary-quadratic rings with a unit group larger than `{±1}`.  For the spiral axis the
relevant ring is the recurrence coefficient ring `ℤ[√−d]` — a unit is a solution of the
norm form `a² + d·b² = 1`.  The content is a one-inequality Diophantine fact:

  * ★★★ `unitForm_generic_axis` — for **every** `d ≥ 2`, the only solutions of
    `a² + d·b² = 1` are `(±1, 0)`: if `b ≠ 0` then `d·b² ≥ d ≥ 2 > 1` already overshoots,
    so `b = 0` and `a² = 1`.  Every axis past the Gaussian one collapses to the bare
    `{±1}` (order `2`).

  * ★★★★ `imaginary_quadratic_unit_trichotomy` — the axis is **exactly** `{2, 4, 6}`:
    generic `ℤ[√−d]` (`d ≥ 2`) has `2` units (`unitForm_generic_axis`), `ℤ[i]` has `4`
    (`ZI_units_exact_four`), `ℤ[ω]` has `6` (`= NS·NT`, `units6_length`).  No fourth value
    occurs — the spiral axis coordinate has a closed finite range, not merely three
    sampled instances.

The proof runs through `Int.natAbs` into `Nat` (the same `∅`-axiom route as
`Tower/DiscForcingObstruction.two_not_a_discriminant`); no `ring`, no `omega`, no
`Classical`.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ImaginaryQuadraticUnitTrichotomy

open E213.Lib.Math.CayleyDickson.Integer.ZI (units4 units4_length)
open E213.Lib.Math.CayleyDickson.Integer.ZOmega (units6 units6_length)

/-! ## §1 — the `Nat` kernel: `a² + d·b² = 1`, `d ≥ 2`, forces `b = 0`, `a = 1` -/

/-- The arithmetic core.  Over `Nat`, with `d ≥ 2`, `aN² + d·bN² = 1` forces `bN = 0` and
    `aN = 1`: a non-zero `bN` makes `d·bN² ≥ 2·1 = 2`, already past `1`; then `aN² = 1`
    forces `aN = 1` (`0` undershoots, `≥ 2` overshoots). -/
theorem nat_unitform_forces (d aN bN : Nat) (hd : 2 ≤ d)
    (h : aN * aN + d * (bN * bN) = 1) : bN = 0 ∧ aN = 1 := by
  rcases bN with _ | bN'
  · -- bN = 0: the equation is `aN² = 1` (by defeq, `d·(0·0) = 0`)
    refine ⟨rfl, ?_⟩
    have h' : aN * aN = 1 := h
    rcases aN with _ | _ | k
    · exact absurd h' (by decide)
    · rfl
    · exfalso
      have hge : 2 * 2 ≤ (k + 2) * (k + 2) :=
        Nat.mul_le_mul (Nat.le_add_left 2 k) (Nat.le_add_left 2 k)
      rw [h'] at hge
      exact absurd hge (by decide)
  · -- bN = bN'+1 ≠ 0: `d·bN² ≥ 2 > 1` overshoots
    exfalso
    have hb1 : 1 ≤ bN' + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hbb : 1 ≤ (bN' + 1) * (bN' + 1) := Nat.mul_le_mul hb1 hb1
    have hd2 : 2 ≤ d * ((bN' + 1) * (bN' + 1)) := Nat.mul_le_mul hd hbb
    have hle : d * ((bN' + 1) * (bN' + 1)) ≤ 1 := by
      have hsum : d * ((bN' + 1) * (bN' + 1))
          ≤ aN * aN + d * ((bN' + 1) * (bN' + 1)) := Nat.le_add_left _ _
      rw [h] at hsum; exact hsum
    exact absurd (Nat.le_trans hd2 hle) (by decide)

/-! ## §2 — the `Int` statement: the generic axis has exactly the two units `±1` -/

/-- ★★★ **Every axis past the Gaussian one is the bare `{±1}`.**  For `d ≥ 2`, the only
    integer solutions of the norm form `a² + d·b² = 1` are `(±1, 0)`.  So the recurrence
    ring `ℤ[√−d]` has unit group `{±1}` of order `2` for every `d ≥ 2` — the spiral axis
    cannot exceed `2` except at the Gaussian (`d = 1`) and Eisenstein (`d = 3`, reduced
    form) points. -/
theorem unitForm_generic_axis (d : Nat) (hd : 2 ≤ d) (a b : Int)
    (h : a * a + (d : Int) * (b * b) = 1) : b = 0 ∧ (a = 1 ∨ a = -1) := by
  rw [← Int.natAbs_mul_self (a := a), ← Int.natAbs_mul_self (a := b)] at h
  rw [← Int.ofNat_mul, ← Int.ofNat_add] at h
  have hnat : a.natAbs * a.natAbs + d * (b.natAbs * b.natAbs) = 1 :=
    Int.ofNat.inj h
  obtain ⟨hbz, haz⟩ := nat_unitform_forces d a.natAbs b.natAbs hd hnat
  refine ⟨?_, ?_⟩
  · -- b = 0 from `b.natAbs = 0`, via `Int.natAbs_eq` (propext-free)
    rcases Int.natAbs_eq b with hb | hb
    · rw [hb, hbz]; rfl
    · rw [hb, hbz]; rfl
  · rcases Int.natAbs_eq a with ha | ha
    · left;  rw [ha, haz]; rfl
    · right; rw [ha, haz]; rfl

/-! ## §3 — the trichotomy: the spiral axis is exhaustively `{2, 4, 6}` -/

/-- ★★★★ **The imaginary-quadratic unit trichotomy.**  The spiral axis coordinate takes
    *exactly* the three values `{2, 4, 6}`, with no fourth:

      * generic `ℤ[√−d]` (`d ≥ 2`): order `2` — the only norm-1 elements are `±1`
        (`unitForm_generic_axis`);
      * Gaussian `ℤ[i]` (`d = 1`): order `4` (`ZI_units_exact_four`, `units4_length`);
      * Eisenstein `ℤ[ω]` (`d = 3`): order `6 = NS·NT` (`units6_length`).

    The classical Dirichlet trichotomy made `∅`-axiom: the axis has a closed finite range,
    not three sampled instances. -/
theorem imaginary_quadratic_unit_trichotomy :
    -- (1) generic axis: every `d ≥ 2` collapses to the two units `±1`
    (∀ (d : Nat), 2 ≤ d → ∀ a b : Int,
        a * a + (d : Int) * (b * b) = 1 → b = 0 ∧ (a = 1 ∨ a = -1))
    -- (2) the Gaussian axis is order 4
    ∧ units4.length = 4
    -- (3) the Eisenstein axis is order 6
    ∧ units6.length = 6 :=
  ⟨fun d hd a b => unitForm_generic_axis d hd a b, units4_length, units6_length⟩

end E213.Lib.Math.CayleyDickson.Integer.ImaginaryQuadraticUnitTrichotomy
