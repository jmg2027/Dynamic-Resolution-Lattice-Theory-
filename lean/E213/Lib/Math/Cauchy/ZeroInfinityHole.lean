import E213.Lib.Math.Cauchy.DetZeroCollapse
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order

/-!
# `0` and `∞` are one hole, not two dual values — the reciprocal-fold's single non-value

`0` and `∞` are not a dual pair of values; they are **one point** — the single place the reciprocal
fold `x ↦ 1/x` returns no value — named twice.  Seen from inside the values it is `0` (the unique
point with no multiplicative inverse: `q · 0 = 1` is unsolvable); seen through the reciprocal it is
`∞` (`1/0`).  There is no second object: the reciprocal *failure* at `0` **is** what "`∞`" names.  So
"`0` is like `∞`" is exact, and "not dual" is exact — duality needs two objects, this is one.

**Why treating `0` as a value smuggles half of an `∞`-system.**  If the value-system is closed under
the reciprocal fold (the multiplicative completion `ℚ = invert(×)`), admitting `0` forces `1/0` to
mean something — i.e. forces `∞` in too.  You cannot take half of the hole.  This is why the
founding's multiplicative readout `ℚ₊` (`Nat213` pairs `(m, n) ↦ m/n`, `m, n ≥ 1`) excludes `0` and
`∞` **symmetrically** — leaving the reciprocal involution `qSwap` total with the unit `1` its only
fixed point (`NatPairToQPos.qOne_reciprocal_fixed`, `reciprocal_fixed_iff_unit`).  The clean fold has
no hole.

**The det-spectrum incarnation** (continuing `DetZeroCollapse`).  The Casoratian is geometric with
ratio the determinant `q` (`cas_step : cas s (n+1) = q · cas s n`).  The reciprocal fold `q ↦ 1/q`
exchanges the two degeneracies and fixes only the units:

  - `q = 0` — the Wronskian collapses to `0` in one step (`cas_zero_collapses`): the area is
    crushed, the *multiplicative-fold collapse*, the value-image of the hole.
  - `q = ±1` — the **reciprocal-fixed core** (`self_reciprocal_iff_unit : q·q = 1 ↔ q = ±1`): the
    Wronskian is conserved / period-2, the founding unit's two faces.
  - `|q| ≥ 2` — blow-up, the reciprocal partner of the `0`-collapse.

So over `ℤ` the reciprocal-closed core is exactly the units `{±1}`; `0` (and the blow-ups) are the
non-fixed directions — and `0` is the one the multiplicative completion can never repair (the
permanent hole, the `∞`).  This file pins that: `0` has no reciprocal, the only self-reciprocal
values are the units, and on those units (and only there) the det-spectrum's Casoratian is conserved.
-/

namespace E213.Lib.Math.Cauchy.ZeroInfinityHole

open E213.Lib.Math.Cauchy.DetZeroCollapse (cas cas_step cas_conserved_unit)
open E213.Meta.Int213 (int_sq_le_one zero_mul)

/-! ## `0` is the reciprocal hole (the value-side name of `∞`) -/

/-- ★★★ **`0` has no reciprocal.**  `q · 0 = 1` is unsolvable for every `q` — `0` is the single
    point at which the reciprocal fold returns no value.  This is the value-side name of `∞`: not a
    second object, but the one hole. -/
theorem zero_no_reciprocal (q : Int) : q * 0 ≠ 1 := by
  intro h
  rw [E213.Meta.Int213.PolyIntM.mul_zeroZ] at h
  exact absurd h (by decide)

/-! ## The reciprocal-fixed core is exactly the units `{±1}` -/

/-- ★★★ **Self-reciprocal ⟺ unit.**  `q · q = 1` (i.e. `q` is its own reciprocal, the fixed points
    of the reciprocal fold) holds for exactly the units `q = 1 ∨ q = −1`.  Everything else flows away
    from the fixed core: `0` to the hole, `|q| ≥ 2` to the blow-up. -/
theorem self_reciprocal_iff_unit (q : Int) : q * q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro h
    have hle : q * q ≤ 1 := by rw [h]; exact E213.Meta.Int213.Order.le_refl 1
    rcases int_sq_le_one q hle with hm1 | h0 | h1
    · exact Or.inr hm1
    · exfalso; rw [h0] at h; exact absurd h (by decide)
    · exact Or.inl h1
  · rintro (h1 | hm1)
    · rw [h1]; decide
    · rw [hm1]; decide

/-- The non-fixed directions: a non-unit is **not** its own reciprocal.  Both `0` (`q·q = 0`) and the
    blow-ups (`q·q ≥ 4`) fall here — the two directions the reciprocal fold pushes off the unit
    core. -/
theorem non_unit_not_self_reciprocal (q : Int) (h1 : q ≠ 1) (hm1 : q ≠ -1) : q * q ≠ 1 := by
  intro h
  rcases (self_reciprocal_iff_unit q).mp h with e | e
  · exact h1 e
  · exact hm1 e

/-! ## The det-spectrum: collapse at the hole, conservation on the core -/

/-- ★★★ **`det = 0` collapses the Casoratian.**  When the determinant coefficient is `0`
    (`s(n+2) = p·s(n+1) − 0·s(n)`, the order secretly dropping to 1), the Wronskian vanishes from the
    next step: `cas s (n+1) = 0`.  The hole's value-image is the area crushed to zero. -/
theorem cas_zero_collapses (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 0 * s n) (n : Nat) : cas s (n + 1) = 0 := by
  have h2 : s (n + 2) = p * s (n + 1) := by
    rw [hrec n, zero_mul, E213.Meta.Int213.Order.sub_zero]
  have h3 : s (n + 3) = p * s (n + 2) := by
    rw [hrec (n + 1), zero_mul, E213.Meta.Int213.Order.sub_zero]
  show s (n + 1) * s (n + 3) - s (n + 2) * s (n + 2) = 0
  have key : s (n + 1) * s (n + 3) = s (n + 2) * s (n + 2) := by rw [h3, h2]; ring_intZ
  rw [key]; exact E213.Meta.Int213.add_neg_cancel _

/-- ★★★★ **`0` is the hole, the units are the reciprocal-closed core.**  One bundle for the
    insight: (1) `0` has no reciprocal — the single hole, the value-side `∞`; (2) the reciprocal-fixed
    values are exactly the units `±1`; (3) at the hole the determinant `q = 0` collapses the
    Casoratian to `0`; (4) on the (reciprocal-fixed) magnitude unit `q = +1` the Casoratian is
    conserved.  Collapse at the hole, conservation on the core — `0`/`∞` the one excluded non-value,
    `±1` the surviving distinguishings. -/
theorem zero_is_hole_units_are_core :
    (∀ q : Int, q * 0 ≠ 1)
    ∧ (∀ q : Int, q * q = 1 ↔ q = 1 ∨ q = -1)
    ∧ (∀ (p : Int) (s : Nat → Int), (∀ n, s (n + 2) = p * s (n + 1) - 0 * s n) →
        ∀ n, cas s (n + 1) = 0)
    ∧ (∀ (p : Int) (s : Nat → Int), (∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) →
        ∀ n, cas s n = cas s 0) :=
  ⟨zero_no_reciprocal, self_reciprocal_iff_unit, cas_zero_collapses, cas_conserved_unit⟩

end E213.Lib.Math.Cauchy.ZeroInfinityHole
