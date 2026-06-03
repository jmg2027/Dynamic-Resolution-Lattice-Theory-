import E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree

/-!
# DiscNegTwoSkipped — why disc −2 is *skipped* between the elliptic axes −3 and −4

The elliptic (finite-order) elements of `SL₂(ℤ)` have integer trace with `|tr| < 2`, i.e.
`tr ∈ {−1, 0, 1}`, giving discriminant `tr² − 4 ∈ {−3, −4}` — exactly the Eisenstein (`ω`, disc
−3, `tr ±1`, order 6) and Gaussian (`i`, disc −4, `tr 0`, order 4) points.  A *negative*
discriminant forces `tr² < 4`, i.e. `|tr| < 2` (elliptic), so the only negative `SL₂(ℤ)`
discriminants are `{−3, −4}`.  **Disc −2 is not among them**: it would need `tr² = 2`, i.e.
`tr = √2 ∉ ℤ` (`no_nat_sqrt_two`).  So disc −2 falls *between* the two elliptic axes and is
skipped on the crystallographic spiral axis `{2,4,6}`; `ℤ[√−2]` carries no exceptional rotation
axis (its unit group is the generic order-2 floor `{±1}`, `ImaginaryQuadraticUnitTrichotomy`'s
`unitForm_generic_axis` at `d = 2`).

Where does `√2` reappear?  **One tier up**: as `2cos(2π/8) = √2`, the trace field of **order 8** —
and `φ(8) = 4 > 2`, the *first non-crystallographic* order (the quadratic-trace lift,
`CyclotomicTraceDegree.cd_lift_orders`: `{1,2,3,4,6} ⊂ {1,2,3,4,5,6,8,10,12}`), where
`√2 = √NT` is the `E₇`-region surd (`why_root_two_and_root_five`).

**Summary**: disc −2 = the skipped point — no integer trace realises it (`√2 ∉ ℕ`); its surd `√2`
is the `√NT` order-8 quadratic-trace lift one tier above the spiral axis `{2,4,6}`; and `ℤ[√−2]`'s
unit group is the order-2 floor `{±1}`.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.DiscNegTwoSkipped

open E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree (phi)
open E213.Lib.Physics.Simplex.Counts (NT)

/-- ★★ **`√2 ∉ ℕ`: `2` is not a perfect square.**  No trace magnitude `m` has `m² = 2`, so no
    discriminant `m² − 4 = −2` is achievable: `m ≤ 1 ⟹ m² ≤ 1 < 2`; `m ≥ 2 ⟹ m² ≥ 4 > 2`. -/
theorem no_nat_sqrt_two : ¬ ∃ n : Nat, n * n = 2 := by
  rintro ⟨n, hn⟩
  match n, hn with
  | 0, h => exact absurd h (by decide)
  | 1, h => exact absurd h (by decide)
  | (k + 2), h =>
      have hle : 2 * 2 ≤ (k + 2) * (k + 2) :=
        Nat.mul_le_mul (Nat.le_add_left 2 k) (Nat.le_add_left 2 k)
      rw [h] at hle
      exact absurd hle (by decide)

/-- ★★★ **The count-Lens-native (below-ℤ) form of the skip: `NT` is a non-square count.**  No
    "discriminant", no "trace", no `ℤ` — purely the count-Lens: `NT = 2` is a count strictly
    *between consecutive count-squares* (`1² < NT < 2²`), so it is the leaf-count of no squared
    chain (`¬ ∃ m, m·m = NT`).  This is the genuinely-foundational reading of "disc −2 skipped":
    the imported `ℤ`-discriminant statement `t² − 4 ≠ −2` is the difference-Lens dressing of this
    one `ℕ` fact — `NT` is non-square, so no count squares to it.  (The signed/`ℤ` framing below is
    the difference-Lens readout; *this* is what survives stripping `ℤ`.) -/
theorem NT_is_nonsquare_count :
    (1 * 1 < NT ∧ NT < 2 * 2) ∧ (¬ ∃ m : Nat, m * m = NT) :=
  ⟨by decide, fun ⟨m, hm⟩ => no_nat_sqrt_two ⟨m, hm⟩⟩

/-- ★★★ **The integer elliptic traces skip disc −2.**  The only `|tr| < 2` integer traces,
    `tr ∈ {−1, 0, 1}`, give discriminants `tr² − 4 ∈ {−3, −4}` — and **none equals −2**.  Since a
    negative discriminant forces `|tr| < 2` (elliptic), `−2` is unreachable by any `SL₂(ℤ)`
    element: it is skipped between the Gaussian axis (−4, order 4) and the Eisenstein axis (−3,
    order 6). -/
theorem elliptic_traces_skip_disc_neg_two :
    ((-1 : Int) * (-1) - 4 = -3 ∧ (0 : Int) * 0 - 4 = -4 ∧ (1 : Int) * 1 - 4 = -3)
    ∧ ((-1 : Int) * (-1) - 4 ≠ -2 ∧ (0 : Int) * 0 - 4 ≠ -2 ∧ (1 : Int) * 1 - 4 ≠ -2) := by
  decide

/-- ★★★ **Disc −2 = the skipped point; its surd `√2 = √NT` is the order-8 quadratic-trace lift.**
    Bundle: (1) the integer elliptic traces skip −2 (`elliptic_traces_skip_disc_neg_two`); (2) −2
    would need a trace magnitude squaring to 2, impossible (`no_nat_sqrt_two` — `√2 ∉ ℕ`); (3) `√2`
    reappears one tier up as the order-8 trace field `√NT` — `φ(8) = 4 > 2`, the first
    non-crystallographic order (off the spiral axis `{2,4,6}` where `φ ≤ 2`), with `NT = 2`. -/
theorem disc_neg_two_skipped :
    (((-1 : Int) * (-1) - 4 ≠ -2) ∧ ((0 : Int) * 0 - 4 ≠ -2) ∧ ((1 : Int) * 1 - 4 ≠ -2))
    ∧ (¬ ∃ n : Nat, n * n = 2)
    ∧ (phi 8 = 4 ∧ ¬ phi 8 ≤ 2 ∧ NT = 2) :=
  ⟨elliptic_traces_skip_disc_neg_two.2, no_nat_sqrt_two, by decide, by decide, by decide⟩

end E213.Lib.Math.CayleyDickson.Tower.DiscNegTwoSkipped
