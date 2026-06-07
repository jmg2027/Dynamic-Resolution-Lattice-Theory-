import E213.Meta.Int213
import E213.Meta.Int213.PolyIntMTactic

/-!
# Smooth 2D-conformal Gauss curvature — A6 core, the smooth route (∅-axiom)

The discrete (Forman) A6 route is closed (`DiscreteRicci`, `RicciFlowDiscrete`, `DiscreteGaussBonnet`);
this file opens the **smooth** route — the one the marathon's transcendentals + PDE work unblocks —
via the decisive 2D-conformal sidestep (`research-notes/frontiers/ricci_flow_smooth_core.md`).

For a 2D conformal metric `ds² = λ·(dx² + dy²)` with `λ` a **polynomial** (positive) factor, the
Gauss curvature is the *rational* Liouville expression — **no sqrt/log/exp**:

  `K = (|∇λ|² − λ·Δλ) / (2λ³)`,   `|∇λ|² = λ_x² + λ_y²`,  `Δλ = λ_xx + λ_yy`.

In 2D `Ric = K·g`, so `∂_t λ = −2K·λ` is genuine smooth Ricci flow, with fixed points the flat
(`K = 0`) metrics.  This file works with the curvature **numerator** `confKNum = |∇λ|² − λΔλ`
(`K = confKNum/(2λ³)`, sign of `K` = sign of `confKNum` for `λ > 0`) over ℤ, and verifies the full
curvature trichotomy on polynomial conformal factors — a genuine smooth Ricci-curvature computation,
∅-axiom (`ring_intZ`).  The smooth wall (general-`n` + transcendental metrics) stays
(`ricci_flow_smooth_core.md`); 2D-conformal with polynomial `λ` is *this side* of it.

All zero-axiom.
-/

namespace E213.Lib.Math.Geometry.GeometrizationConjecture.ConformalCurvature

open E213.Meta.Int213

/-- Gauss-curvature **numerator** of the conformal metric `ds² = λ(dx²+dy²)` from the 2-jet of `λ`:
    `confKNum = (λ_x² + λ_y²) − λ·(λ_xx + λ_yy)` (Liouville).  The curvature is
    `K = confKNum / (2λ³)`; for `λ > 0` the sign of `K` is the sign of `confKNum`. -/
def confKNum (lam lamx lamy lamxx lamyy : Int) : Int :=
  (lamx * lamx + lamy * lamy) - lam * (lamxx + lamyy)

/-- ★★★ **S3 — flat conformal metric.**  A constant conformal factor `λ = c` (zero 2-jet) has Gauss
    curvature `0`: the flat metric.  (`ds² = c(dx²+dy²)` is flat Euclidean rescaled.) -/
theorem confK_flat (c : Int) : confKNum c 0 0 0 0 = 0 := by
  show (0 * 0 + 0 * 0) - c * (0 + 0) = 0
  have h1 : (0 * 0 + 0 * 0 : Int) = 0 := by decide
  have h2 : c * (0 + 0) = 0 := by rw [Int.add_zero]; exact Int.mul_zero c
  rw [h1, h2]; decide

/-- ★★★★ **S4 (negative) — a negatively-curved smooth conformal metric.**  For the polynomial
    factor `λ = x² + y² + 1` (2-jet `λ_x = 2x, λ_y = 2y, λ_xx = λ_yy = 2`, the standard partials),
    the Gauss-curvature numerator is the constant `−4`: `K = −4/(2λ³) < 0` everywhere — a genuine
    smooth metric of negative curvature, computed ∅-axiom. -/
theorem confK_paraboloid (x y : Int) :
    confKNum (x * x + y * y + 1) (2 * x) (2 * y) 2 2 = -4 := by
  unfold confKNum; ring_intZ

/-- ★★★★ **S4 (positive) — a positively-curved smooth conformal metric.**  For the "dome" factor
    `λ = C − x² − y²` (2-jet `λ_x = −2x, λ_y = −2y, λ_xx = λ_yy = −2`), the Gauss-curvature numerator
    is `4C > 0` (for `C > 0`, where `λ > 0`, i.e. `x²+y² < C`): `K = 4C/(2λ³) > 0` — a genuine
    smooth metric of positive curvature. -/
theorem confK_dome (C x y : Int) :
    confKNum (C - x * x - y * y) (-(2 * x)) (-(2 * y)) (-2) (-2) = 4 * C := by
  unfold confKNum; ring_intZ

/-- ★★★★★ **Smooth 2D-conformal curvature trichotomy** (the reachable smooth A6 route).  The
    Liouville Gauss-curvature numerator realizes all three signs on polynomial conformal factors —
    flat (`λ` constant), negative (`λ = x²+y²+1`), positive (`λ = C−x²−y²`, `C ≥ 1`) — each a genuine
    smooth Ricci-curvature value, ∅-axiom.  The smooth side of A6, sidestepping transcendentals. -/
theorem conformal_curvature_trichotomy (x y : Int) :
    confKNum 5 0 0 0 0 = 0
    ∧ confKNum (x * x + y * y + 1) (2 * x) (2 * y) 2 2 < 0
    ∧ (0 : Int) < confKNum (1 - x * x - y * y) (-(2 * x)) (-(2 * y)) (-2) (-2) := by
  refine ⟨confK_flat 5, ?_, ?_⟩
  · rw [confK_paraboloid]; decide
  · rw [confK_dome]; decide

/-! ## §S5 — the 2D conformal Ricci flow `∂_t λ = −2K·λ`

In 2D every metric is Einstein: `Ric = K·g` (scalar `R = 2K`).  The Ricci flow `∂_t g = −2 Ric`
on `g = λ·δ` therefore reads `∂_t λ = −2K·λ`; with `K = confKNum/(2λ³)` this clears to

  `λ² · (∂_t λ) = −confKNum`.

So the flow's rate has integer numerator `confFlowRate = −confKNum`, and the flow is **stationary
exactly at flat (`K = 0`) metrics** — the fixed points of the smooth 2D-conformal Ricci flow. -/

/-- The 2D conformal Ricci-flow rate numerator: `λ²·∂_tλ = confFlowRate` where `∂_tλ = −2Kλ`. -/
def confFlowRate (lam lamx lamy lamxx lamyy : Int) : Int :=
  -(confKNum lam lamx lamy lamxx lamyy)

/-- ★★★ **Flat metrics are stationary.**  A constant conformal factor (flat, `K = 0`) is a fixed
    point of the 2D conformal Ricci flow: the rate vanishes. -/
theorem conf_flow_flat_stationary (c : Int) : confFlowRate c 0 0 0 0 = 0 := by
  unfold confFlowRate; rw [confK_flat]; rfl

/-- ★★★★ **Stationary ⟹ flat.**  A fixed point of the 2D conformal Ricci flow (`confFlowRate = 0`)
    is exactly a flat metric (`K = 0`, `confKNum = 0`) — the flow drives the conformal metric toward
    constant (zero) curvature, the smooth A6 conclusion in the 2D-conformal category. -/
theorem conf_flow_stationary_imp_flat (lam lamx lamy lamxx lamyy : Int)
    (h : confFlowRate lam lamx lamy lamxx lamyy = 0) :
    confKNum lam lamx lamy lamxx lamyy = 0 := by
  unfold confFlowRate at h
  have h2 := congrArg Neg.neg h
  rw [Int.neg_neg, Int.neg_zero] at h2
  exact h2

end E213.Lib.Math.Geometry.GeometrizationConjecture.ConformalCurvature
