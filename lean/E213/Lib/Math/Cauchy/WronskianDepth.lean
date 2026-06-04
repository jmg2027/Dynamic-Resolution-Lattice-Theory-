import E213.Lib.Math.Cauchy.DetZeroCollapse
import E213.Lib.Math.Cauchy.PolyDepthMonotone
import E213.Meta.Int213.Core

/-!
# The unit's two faces have opposite additive-depth status

The det spectrum (`DetZeroCollapse`) read `det = ±1` as the founding unit's two faces — `+1` the
*magnitude* (Wronskian conserved), `−1` the *sign* (Wronskian period-2).  Under the **additive**
reading (finite difference-depth), these two faces are *opposite*:

  - **`det = +1`** — the conserved Wronskian is **constant**, so `polyDepthZ 0` — additively trivial
    (the magnitude unit is depth-0).
  - **`det = −1`** — the period-2 Wronskian (`Wₙ₊₂ = Wₙ`, sign-flipping, non-constant when `W₀ ≠ 0`)
    is **not eventually monotone**, so has **no finite depth** at all — additively maximal (the sign
    unit is the simplest infinite-depth object, a pure period-2 oscillation).

So the single multiplicative unit, viewed through the additive fold, *splits*: its magnitude is
additively empty, its sign is additively inexhaustible.  This is the sharpest expression of the
additive/multiplicative (depth/order) duality on one object — the Wronskian — and it pins *why* the
sign (the founding period-2 swap, `NT = 2`) is the carrier of additive richness.
-/

namespace E213.Lib.Math.Cauchy.WronskianDepth

open E213.Lib.Math.Cauchy.DetZeroCollapse (cas cas_step cas_conserved_unit cas_period2_neg_unit)
open E213.Lib.Math.Cauchy.PolyDepthMonotone (MonoFromZ AntiFromZ polyDepthZ_evMono)
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ)
open E213.Meta.Int213.Order (le_antisymm)

/-- **`det = +1`: the Wronskian is depth-0.**  Conserved (`cas s n = cas s 0`) *is* `polyDepthZ 0`:
    the magnitude-unit orbit's Wronskian is additively trivial. -/
theorem cas_unit_depth0 (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) : polyDepthZ 0 (cas s) :=
  cas_conserved_unit p s hrec

/-! ## `det = −1`: period-2, non-constant ⟹ no finite depth -/


/-- `x ≠ 0 ⟹ (-1)·x ≠ 0`. -/
theorem neg_one_mul_ne_zero {x : Int} (h : x ≠ 0) : (-1) * x ≠ 0 := by
  intro he
  apply h
  have hx : x = (-1) * ((-1) * x) := by ring_intZ
  rw [he, E213.Meta.Int213.PolyIntM.mul_zeroZ] at hx
  exact hx

/-- For the `det = −1` orbit with `W₀ ≠ 0`, the Wronskian never vanishes. -/
theorem cas_neg_unit_ne_zero (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - (-1) * s n) (h0 : cas s 0 ≠ 0) :
    ∀ n, cas s n ≠ 0 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => rw [cas_step p (-1) s hrec n]; exact neg_one_mul_ne_zero ih

/-- Consecutive Wronskian values differ (sign-flip, nonzero). -/
theorem cas_neg_unit_consecutive_ne (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - (-1) * s n) (h0 : cas s 0 ≠ 0) :
    ∀ n, cas s n ≠ cas s (n + 1) := by
  intro n
  rw [cas_step p (-1) s hrec n, show (-1) * cas s n = -(cas s n) by ring_intZ]
  exact E213.Meta.Int213.int_ne_neg_self (cas_neg_unit_ne_zero p s hrec h0 n)

/-- A period-2 sequence whose consecutive terms always differ is **not eventually monotone**
    (neither non-decreasing nor non-increasing). -/
theorem period2_nonconst_not_evMono (s : Nat → Int) (hper : ∀ n, s (n + 2) = s n)
    (hne : ∀ n, s n ≠ s (n + 1)) :
    ¬ ((∃ N, MonoFromZ N s) ∨ (∃ N, AntiFromZ N s)) := by
  rintro (⟨N, hmono⟩ | ⟨N, hanti⟩)
  · have h1 : s N ≤ s (N + 1) := hmono N (N + 1) (Nat.le_refl N) (Nat.le_succ N)
    have h2 : s (N + 1) ≤ s (N + 2) := hmono (N + 1) (N + 2) (Nat.le_succ N) (Nat.le_succ (N + 1))
    rw [hper N] at h2
    exact hne N (le_antisymm h1 h2)
  · have h1 : s (N + 1) ≤ s N := hanti N (N + 1) (Nat.le_refl N) (Nat.le_succ N)
    have h2 : s (N + 2) ≤ s (N + 1) := hanti (N + 1) (N + 2) (Nat.le_succ N) (Nat.le_succ (N + 1))
    rw [hper N] at h2
    exact hne N (le_antisymm h2 h1)

/-- ★★★ **`det = −1`: the Wronskian has no finite depth.**  Period-2 (`cas_period2_neg_unit`) and
    non-constant (`cas_neg_unit_consecutive_ne`, when `W₀ ≠ 0`) ⟹ not eventually monotone ⟹ not
    `polyDepthZ d` for any `d` (via `polyDepthZ_evMono`).  The sign-unit is additively
    inexhaustible. -/
theorem cas_neg_unit_no_finite_depth (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - (-1) * s n) (h0 : cas s 0 ≠ 0) :
    ¬ ∃ d, polyDepthZ d (cas s) := by
  rintro ⟨d, hpd⟩
  exact period2_nonconst_not_evMono (cas s) (cas_period2_neg_unit p s hrec)
    (cas_neg_unit_consecutive_ne p s hrec h0) (polyDepthZ_evMono d (cas s) hpd)

/-- ★★★★ **The unit's two faces have opposite additive-depth status.**  `det = +1` (magnitude):
    the Wronskian is `polyDepthZ 0` (additively trivial).  `det = −1` (sign, `W₀ ≠ 0`): the Wronskian
    has no finite depth (additively maximal — a period-2 oscillation).  One multiplicative unit, two
    opposite additive readings. -/
theorem unit_faces_opposite_depth (p : Int) (s : Nat → Int) :
    (∀ _ : (∀ n, s (n + 2) = p * s (n + 1) - 1 * s n), polyDepthZ 0 (cas s))
    ∧ (∀ _ : (∀ n, s (n + 2) = p * s (n + 1) - (-1) * s n), cas s 0 ≠ 0 →
        ¬ ∃ d, polyDepthZ d (cas s)) :=
  ⟨fun hrec => cas_unit_depth0 p s hrec, fun hrec h0 => cas_neg_unit_no_finite_depth p s hrec h0⟩

end E213.Lib.Math.Cauchy.WronskianDepth
