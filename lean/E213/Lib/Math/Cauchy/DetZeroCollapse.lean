import E213.Lib.Math.Cauchy.EllipticPeriodicTier
import E213.Meta.Int213.PolyIntMTactic

/-!
# `det = 0` is the ratio-Lens collapse — the natural degeneracy, not a forced case

The Cassini cross-determinant `cas s n = s n · s(n+2) − s(n+1)²` is the discrete **Wronskian** of the
order-2 orbit: it measures whether the two solution-shifts `(s n, s(n+1))` and `(s(n+1), s(n+2))` are
linearly independent.  So `det = 0` is not a case to be force-fitted — it is the **collapse**:

  - linear-algebra: the companion is singular, the orbit froze to a *line* (1-dimensional), a
    dimension was crushed;
  - the **ratio-Lens (ℚ = invert(×)) reads one value**: `cas s n = 0 ⟺ s n · s(n+2) = s(n+1)² ⟺
    s(n+1)/s(n) = s(n+2)/s(n+1)` — consecutive multiplicative quotients *coincide*, i.e. the orbit is
    a single geometric ray `s(n) = c·rⁿ`, one ratio `r` with no remainder.

So `det` *is* the ratio-Lens's spread — the surviving-distinguishing of the multiplicative fold;
`det = 0` is zero spread (one quotient), `det = ±1` (the unit) is the Cassini floor where the orbit
stays full-dimensional and never freezes (`CassiniDepthFloor.conserved_never_degenerate`).

**The two fold-collapses.**  `det = 0` and `disc = tr² − 4·det = 0` are *different* degeneracies, one
per founding fold:
  - **`det = 0`** — the **multiplicative** fold (ℚ, ratio-Lens) collapses: ratio → one value, a pure
    geometric ray (`geometric_cas_zero` below); the additive structure is absent.
  - **`disc = 0`** — the **additive** fold (ℤ, difference-Lens) degenerates: the two eigenvalues
    coincide (repeated root), introducing the polynomial mode `n·λⁿ` — exactly `polyDepthZ 1`
    (`EllipticPeriodicTier.parabolic_iff_depth1`).
Both are "everything collapses to one value", read in the two folds the number tower is built from.
-/

namespace E213.Lib.Math.Cauchy.DetZeroCollapse

open E213.Lib.Math.Real213.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.Cauchy.EllipticPeriodicTier (comp comp_det)

/-- The Cassini cross-determinant (discrete Wronskian) of the order-2 orbit. -/
def cas (s : Nat → Int) (n : Nat) : Int := s n * s (n + 2) - s (n + 1) * s (n + 1)

/-- ★★★ **`det = 0` is the geometric collapse.**  An order-1 (single-ratio) orbit `s(n+1) = r·s(n)`
    — the degenerate case where the multiplicative quotient is *one value* `r` — has Cassini
    determinant identically `0`.  The Wronskian vanishes exactly when the two solution-shifts are
    dependent, i.e. the orbit is a single geometric ray. -/
theorem geometric_cas_zero (r : Int) (s : Nat → Int) (hrec : ∀ n, s (n + 1) = r * s n) :
    ∀ n, cas s n = 0 := by
  intro n
  have h1 : s (n + 2) = r * s (n + 1) := hrec (n + 1)
  have h2 : s (n + 1) = r * s n := hrec n
  show s n * s (n + 2) - s (n + 1) * s (n + 1) = 0
  have key : s n * s (n + 2) = s (n + 1) * s (n + 1) := by rw [h1, h2]; ring_intZ
  rw [key]
  exact E213.Meta.Int213.add_neg_cancel _

/-- ★★★ **`det = 0` ⟺ the order drops, naturally.**  At the companion, `det (comp p 0) = 0` — the
    discriminant's determinant datum vanishing *is* `q = 0`, the `s(n)` coefficient forgotten, the
    order-2 recurrence secretly order-1 (`s(n+2) = p·s(n+1)`); and any single-ratio orbit has Cassini
    `≡ 0`.  `det = 0` is the multiplicative-fold collapse, not a force-fit. -/
theorem det_zero_is_ratio_collapse :
    (∀ p : Int, Mat2.det (comp p 0) = 0)
    ∧ (∀ (r : Int) (s : Nat → Int), (∀ n, s (n + 1) = r * s n) → ∀ n, cas s n = 0) :=
  ⟨fun p => comp_det p 0, fun r s hrec => geometric_cas_zero r s hrec⟩

/-! ## `det` is the geometric ratio of the orbit's own Wronskian

The Cassini cross-determinant `cas` of an order-2 orbit is **itself a single geometric sequence**,
with ratio exactly the companion determinant `q`: `cas s (n+1) = q · cas s n`.  So the order-2
orbit's Wronskian is *order 1* (the Casoratian drops the order by one), and `det = q` is the
per-step multiplier of the discrete area / surviving distinguishing.  This places the whole `det`
spectrum at once:

  - `q = 0`   — ratio `0`: the area collapses to `0` immediately (`geometric_cas_zero`); the orbit
    is a degenerate geometric ray, the multiplicative-fold collapse.
  - `q = ±1`  — ratio a *unit*: the area is conserved (`|cas|` constant) — the Cassini/`SL₂` floor,
    the founding unit `det P = NS − NT`, the live full-dimensional (elliptic/hyperbolic) orbit.
  - `|q| ≥ 2` — ratio of magnitude `> 1`: the area expands geometrically `|cas s n| = |q|ⁿ·|cas s 0|`.

So `det` is not a quantity to force-fit: it *is* the orbit's area-multiplier, and its value (relative
to the unit `±1`) reads off collapse / conservation / expansion. -/

/-- ★★★ **The Wronskian is geometric with ratio `det`.**  For `s(n+2) = p·s(n+1) − q·s(n)`, the
    Cassini determinant satisfies `cas s (n+1) = q · cas s n` — the companion det `q` is the
    geometric ratio of the orbit's own Wronskian (the middle coefficient `p` cancels). -/
theorem cas_step (p q : Int) (s : Nat → Int) (hrec : ∀ n, s (n + 2) = p * s (n + 1) - q * s n)
    (n : Nat) : cas s (n + 1) = q * cas s n := by
  have h2 : s (n + 2) = p * s (n + 1) - q * s n := hrec n
  have h3 : s (n + 3) = p * s (n + 2) - q * s (n + 1) := hrec (n + 1)
  show s (n + 1) * s (n + 3) - s (n + 2) * s (n + 2)
      = q * (s n * s (n + 2) - s (n + 1) * s (n + 1))
  rw [h3, h2]; ring_intZ

/-! ## The two units `det = ±1` are the founding's two faces of the unit

`cas_step` makes the unimodular floor concrete and ties it to the number-tower founding's reading of
the unit `1 = NS − NT` (`SharedUnitAcrossReadings`), which is *magnitude `1` with sign `±`*:

  - **`det = +1`** — the Wronskian is **conserved** (`cas s n = cas s 0`): the orbit is exactly
    area-preserving, `SL₂`, the founding unit's *magnitude* face.
  - **`det = −1`** — the Wronskian is **period-2** (`cas s (n+2) = cas s n`, flipping sign each
    step): the founding unit's *sign* face — the period-2 swap (`PairCompletion.swap_order_eq_NT`,
    `NT = 2`) that the founding reads as negation.

So the two unimodular dets are exactly the founding unit's (magnitude, sign) — conservation and the
period-2 swap — the same `±1` that floors the discriminant dial (`EllipticPeriodicTier`, elliptic
`comp 0 1 = S`, `comp 1 1 = U`). -/

/-- ★★★ **`det = +1`: the Wronskian is conserved.**  `s(n+2) = p·s(n+1) − s(n)` ⟹ `cas s n =
    cas s 0` — exact area preservation, the founding unit's magnitude face (`SL₂`). -/
theorem cas_conserved_unit (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) : ∀ n, cas s n = cas s 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [cas_step p 1 s hrec n, E213.Meta.Int213.PolyIntM.one_mulZ, ih]

/-- ★★★ **`det = −1`: the Wronskian is period-2.**  `s(n+2) = p·s(n+1) + s(n)` ⟹
    `cas s (n+2) = cas s n` — the founding unit's sign face, the period-2 swap (`NT = 2`). -/
theorem cas_period2_neg_unit (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - (-1) * s n) : ∀ n, cas s (n + 2) = cas s n := by
  intro n
  have e1 : cas s (n + 1) = (-1) * cas s n := cas_step p (-1) s hrec n
  have e2 : cas s (n + 2) = (-1) * cas s (n + 1) := cas_step p (-1) s hrec (n + 1)
  rw [e2, e1]; ring_intZ

end E213.Lib.Math.Cauchy.DetZeroCollapse
