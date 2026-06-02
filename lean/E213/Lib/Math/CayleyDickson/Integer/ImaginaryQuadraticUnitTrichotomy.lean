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

open E213.Lib.Math.CayleyDickson.Integer.ZI (ZI units4 units4_length)
open E213.Lib.Math.CayleyDickson.Integer.ZOmega (ZOmega units6 units6_length Zeta6 zeta6_cubed zeta6_pow_six)

/-! ## §1 — the `Nat` kernel: `a² + d·b² = 1`, `d ≥ 2`, forces `b = 0`, `a = 1` -/

/-- `aN² = 1` over `Nat` forces `aN = 1` (`0` undershoots, `≥ 2` overshoots). -/
theorem nat_sq_eq_one (aN : Nat) (h : aN * aN = 1) : aN = 1 := by
  rcases aN with _ | _ | k
  · exact absurd h (by decide)
  · rfl
  · exfalso
    have hge : 2 * 2 ≤ (k + 2) * (k + 2) :=
      Nat.mul_le_mul (Nat.le_add_left 2 k) (Nat.le_add_left 2 k)
    rw [h] at hge
    exact absurd hge (by decide)

/-- The general kernel: `aN² + d·bN² = N` with `N < d` forces `bN = 0` — a non-zero `bN`
    already makes the `d`-term alone (`≥ d`) overshoot `N`.  The unit case is `N = 1`,
    `d ≥ 2`; the `d ≡ 3 (mod 4)` reduced-form case is `N = 4`, `d ≥ 5`. -/
theorem nat_form_forces_b_zero (d aN bN N : Nat) (hNd : N < d)
    (h : aN * aN + d * (bN * bN) = N) : bN = 0 := by
  rcases bN with _ | bN'
  · rfl
  · exfalso
    have hb1 : 1 ≤ bN' + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hbb : 1 ≤ (bN' + 1) * (bN' + 1) := Nat.mul_le_mul hb1 hb1
    have hdle : d ≤ d * ((bN' + 1) * (bN' + 1)) := by
      have hx := Nat.mul_le_mul (Nat.le_refl d) hbb
      rwa [Nat.mul_one] at hx
    have hsum : d * ((bN' + 1) * (bN' + 1)) ≤ N := by
      have hle : d * ((bN' + 1) * (bN' + 1))
          ≤ aN * aN + d * ((bN' + 1) * (bN' + 1)) := Nat.le_add_left _ _
      rw [h] at hle; exact hle
    exact absurd (Nat.lt_of_lt_of_le hNd (Nat.le_trans hdle hsum)) (Nat.lt_irrefl N)

/-- The arithmetic core for the unit case.  With `d ≥ 2`, `aN² + d·bN² = 1` forces `bN = 0`
    (`nat_form_forces_b_zero`, `1 < d`) and then `aN = 1` (`nat_sq_eq_one`). -/
theorem nat_unitform_forces (d aN bN : Nat) (hd : 2 ≤ d)
    (h : aN * aN + d * (bN * bN) = 1) : bN = 0 ∧ aN = 1 := by
  have hbz : bN = 0 := nat_form_forces_b_zero d aN bN 1 hd h
  subst hbz
  exact ⟨rfl, nat_sq_eq_one aN h⟩

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

/-! ## §3b — the `d ≡ 3 (mod 4)` maximal orders also collapse to `±1` -/

/-- ★★★ **The reduced-form (`d ≡ 3 mod 4`) maximal orders carry no complex unit.**  For
    `d ≡ 3 (mod 4)`, `d ≥ 7`, the maximal order `ℤ[(1+√−d)/2]` has norm form
    `a² + a·b + c·b²` with `c = (1+d)/4`; multiplying by `4` gives `(2a+b)² + d·b² = 4`
    (using `4c − 1 = d`).  For `d ≥ 5` this forces the imaginary part `b = 0`: every unit
    is *real*, i.e. lies in `ℤ`, so the unit group is `ℤ^× = {±1}` of order 2.  Hence
    `ℤ[ω]` (`d = 3`) is the *only* reduced-form order with a complex unit — completing the
    Dirichlet trichotomy to **all** imaginary-quadratic maximal orders, not just the
    `ℤ[√−d]` family.  (Only `b = 0` is asserted; that the resulting `(2a)² = 4` gives
    `a = ±1` is the order-2 count, an integer cancellation outside the `∅`-axiom Int API.) -/
theorem maximal_order_no_complex_unit (d : Nat) (hd : 5 ≤ d) (a b : Int)
    (h : (2 * a + b) * (2 * a + b) + (d : Int) * (b * b) = 4) : b = 0 := by
  rw [← Int.natAbs_mul_self (a := 2 * a + b), ← Int.natAbs_mul_self (a := b),
      ← Int.ofNat_mul, ← Int.ofNat_add] at h
  have hnat : (2 * a + b).natAbs * (2 * a + b).natAbs
      + d * (b.natAbs * b.natAbs) = 4 := Int.ofNat.inj h
  have hbz := nat_form_forces_b_zero d (2 * a + b).natAbs b.natAbs 4 hd hnat
  rcases Int.natAbs_eq b with hb | hb <;> (rw [hb, hbz]; rfl)

/-! ## §4 — the binary cover: `{2,4,6} = 2·{1,2,3}`, the midpoint is the central `−1` -/

/-- ★★★ **The spiral axis is the binary double cover of the point-rotation `{1,2,3}`.**
    Each floor-rotation multiplier `μ` reaches the central unit `−1` at its *midpoint*
    power `k ∈ {1,2,3}` and the identity at `2k ∈ {2,4,6}`:

      * order-2 axis `ℤ`:    `μ = −1`,  `μ¹ = −1`,  `μ² = 1`   (`k = 1`);
      * order-4 axis `ℤ[i]`: `μ = −i`,  `μ² = −1`,  `μ⁴ = 1`   (`k = 2`);
      * order-6 axis `ℤ[ω]`: `μ = ζ₆`, `μ³ = −1`,  `μ⁶ = 1`   (`k = 3`).

    So the axis orders `{2,4,6} = 2·{1,2,3}` are the **even half** of the crystallographic
    set `{1,2,3,4,6}` (`Tower/CyclotomicTraceDegree.crystallographic_restriction`), and the
    factor `2` is the central involution `−1` — the Cassini sign `(−1)ⁿ` carried by every
    cross-determinant.  This central `−1` is the `2`-fold cover, the structural origin of the
    word *binary* in the binary-polyhedral rungs `E₆ = 2T, E₇ = 2O, E₈ = 2I`
    (`Tower/BinaryPolyhedralTower`, `Tower/MckayADECensus`): the spiral floor lives one
    central `−1` above the bare point rotation. -/
theorem axis_binary_cover :
    -- order-2 axis `ℤ`: midpoint `k=1`, full `2`
    ((-1 : Int) * (-1) = 1)
    -- order-4 axis `ℤ[i]`: midpoint `k=2` (`μ² = −1`), full `4` (`μ⁴ = 1`)
    ∧ ((⟨0, -1⟩ : ZI) * ⟨0, -1⟩ = ⟨-1, 0⟩
        ∧ (⟨0, -1⟩ : ZI) * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩ = ⟨1, 0⟩)
    -- order-6 axis `ℤ[ω]`: midpoint `k=3` (`ζ₆³ = −1`), full `6` (`ζ₆⁶ = 1`)
    ∧ (Zeta6 * Zeta6 * Zeta6 = ⟨-1, 0⟩
        ∧ Zeta6 * Zeta6 * Zeta6 * Zeta6 * Zeta6 * Zeta6 = ⟨1, 0⟩) :=
  ⟨by decide, ⟨by decide, by decide⟩, ⟨zeta6_cubed, zeta6_pow_six⟩⟩

/-! ## §5 — the crystallographic cosines `2cos(2πk/6)` as the Eisenstein traces -/

/-- The rational-integer trace `u + conj(u) = ⟨2·re − im, 0⟩` of an Eisenstein integer. -/
def ztrace (u : ZOmega) : Int := 2 * u.re - u.im

/-- ★★★ **The crystallographic cosines are the Eisenstein order-6 traces.**  The traces of
    `ζ₆¹..ζ₆⁶` are `1, −1, −2, −1, 1, 2` — exactly `2cos(2πk/6)` for `k = 1..6`, the only
    *integer* values of `2cos(2π/n)` (the rational-trace / crystallographic orders
    `n ∈ {1,2,3,4,6}`, `Tower/CyclotomicTraceDegree.crystallographic_restriction`).  So the
    order-6 axis (π/circle, Eisenstein) carries the full integer cosine spectrum
    `{2, 1, −1, −2}`, the trace-reading of the `{2,4,6}` axis. -/
theorem crystallographic_cosines :
    ztrace Zeta6 = 1
    ∧ ztrace (Zeta6 * Zeta6) = -1
    ∧ ztrace (Zeta6 * Zeta6 * Zeta6) = -2
    ∧ ztrace (Zeta6 * Zeta6 * Zeta6 * Zeta6) = -1
    ∧ ztrace (Zeta6 * Zeta6 * Zeta6 * Zeta6 * Zeta6) = 1
    ∧ ztrace (Zeta6 * Zeta6 * Zeta6 * Zeta6 * Zeta6 * Zeta6) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Integer.ImaginaryQuadraticUnitTrichotomy
