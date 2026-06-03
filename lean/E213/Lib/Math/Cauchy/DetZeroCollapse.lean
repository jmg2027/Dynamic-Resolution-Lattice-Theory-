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

end E213.Lib.Math.Cauchy.DetZeroCollapse
