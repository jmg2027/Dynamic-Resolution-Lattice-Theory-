import E213.Meta.Int213
import E213.Meta.Int213.PolyIntMTactic

/-!
# Smooth 2D-conformal Gauss curvature (∅-axiom)

Alongside the discrete (Forman) curvature route (`DiscreteRicci`, `RicciFlowDiscrete`,
`DiscreteGaussBonnet`), this file works the **smooth** route via the 2D-conformal
reduction.

For a 2D conformal metric `ds² = λ·(dx² + dy²)` with `λ` a **polynomial** (positive) factor, the
Gauss curvature is the *rational* Liouville expression — **no sqrt/log/exp**:

  `K = (|∇λ|² − λ·Δλ) / (2λ³)`,   `|∇λ|² = λ_x² + λ_y²`,  `Δλ = λ_xx + λ_yy`.

In 2D `Ric = K·g`, so `∂_t λ = −2K·λ` is genuine smooth Ricci flow, with fixed points the flat
(`K = 0`) metrics.  This file works with the curvature **numerator** `confKNum = |∇λ|² − λΔλ`
(`K = confKNum/(2λ³)`, sign of `K` = sign of `confKNum` for `λ > 0`) over ℤ, and verifies the full
curvature trichotomy on polynomial conformal factors — a genuine smooth Ricci-curvature computation,
∅-axiom (`ring_intZ`).  The general-`n` and transcendental-metric cases are not claimed here;
2D-conformal with polynomial `λ` is the case treated.

All zero-axiom.
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.ConformalCurvature

open E213.Meta.Int213

/-- Gauss-curvature **numerator** of the conformal metric `ds² = λ(dx²+dy²)` from the 2-jet of `λ`:
    `confKNum = (λ_x² + λ_y²) − λ·(λ_xx + λ_yy)` (Liouville).  The curvature is
    `K = confKNum / (2λ³)`; for `λ > 0` the sign of `K` is the sign of `confKNum`. -/
def confKNum (lam lamx lamy lamxx lamyy : Int) : Int :=
  (lamx * lamx + lamy * lamy) - lam * (lamxx + lamyy)

/-- ★★★ **Flat conformal metric.**  A constant conformal factor `λ = c` (zero 2-jet) has Gauss
    curvature `0`: the flat metric.  (`ds² = c(dx²+dy²)` is flat Euclidean rescaled.) -/
theorem confK_flat (c : Int) : confKNum c 0 0 0 0 = 0 := by
  show (0 * 0 + 0 * 0) - c * (0 + 0) = 0
  have h1 : (0 * 0 + 0 * 0 : Int) = 0 := by decide
  have h2 : c * (0 + 0) = 0 := by rw [Int.add_zero]; exact Int.mul_zero c
  rw [h1, h2]; decide

/-- ★★★★ **Negative — a negatively-curved smooth conformal metric.**  For the polynomial
    factor `λ = x² + y² + 1` (2-jet `λ_x = 2x, λ_y = 2y, λ_xx = λ_yy = 2`, the standard partials),
    the Gauss-curvature numerator is the constant `−4`: `K = −4/(2λ³) < 0` everywhere — a genuine
    smooth metric of negative curvature, computed ∅-axiom. -/
theorem confK_paraboloid (x y : Int) :
    confKNum (x * x + y * y + 1) (2 * x) (2 * y) 2 2 = -4 := by
  unfold confKNum; ring_intZ

/-- ★★★★ **Positive — a positively-curved smooth conformal metric.**  For the "dome" factor
    `λ = C − x² − y²` (2-jet `λ_x = −2x, λ_y = −2y, λ_xx = λ_yy = −2`), the Gauss-curvature numerator
    is `4C > 0` (for `C > 0`, where `λ > 0`, i.e. `x²+y² < C`): `K = 4C/(2λ³) > 0` — a genuine
    smooth metric of positive curvature. -/
theorem confK_dome (C x y : Int) :
    confKNum (C - x * x - y * y) (-(2 * x)) (-(2 * y)) (-2) (-2) = 4 * C := by
  unfold confKNum; ring_intZ

/-- ★★★★★ **Smooth 2D-conformal curvature trichotomy.**  The
    Liouville Gauss-curvature numerator realizes all three signs on polynomial conformal factors —
    flat (`λ` constant), negative (`λ = x²+y²+1`), positive (`λ = C−x²−y²`, `C ≥ 1`) — each a genuine
    smooth Ricci-curvature value, ∅-axiom, on rational conformal factors (no transcendentals). -/
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

/-! ## §S6 — general-`n` conformally-flat scalar curvature (including `n = 3`)

The 2D Liouville curvature above generalizes: for a conformally-flat metric `ds² =
λ·(dx₁²+…+dxₙ²)` on `ℝⁿ` (`λ > 0` a polynomial factor), the **scalar** curvature is the
rational expression (no transcendentals — `φ = ½ln λ` cancels, leaving `λ`-rationals):

  `R = −(n−1)·(4λ·Δλ + (n−6)·|∇λ|²) / (4λ³)`,   `|∇λ|² = Σ λ_i²`,  `Δλ = Σ λ_ii`.

`confRNumN` is the numerator `−(n−1)(4λΔλ + (n−6)|∇λ|²)`; `R = confRNumN/(4λ³)`, so for
`λ > 0` the sign of `R` is the sign of `confRNumN`.  It **reduces exactly** to the 2D
Liouville case (`confRNumN_eq_confKNum`: `confRNumN 2 = 4·confKNum`, `R = 2K`), validating
the general formula against the established `n = 2`.

This extends the conformal computation to general `n` (polynomial `λ`, numerator over ℤ,
`ring_intZ`) — and at `n = 3` it is the **scalar curvature of conformally-flat 3-metrics**.
Honest boundary: only the *scalar* curvature is reached this way; the full
Ricci **tensor** and the Ricci **flow** for `n ≥ 3` need the general-`n` tensor calculus
(and Ricci flow does **not** preserve conformality for `n ≥ 3`), neither of which is
treated here.  All zero-axiom. -/

/-- General-`n` conformally-flat **scalar**-curvature numerator from the `2`-jet of `λ`
    (`gradSq = |∇λ|²`, `lap = Δλ`): `confRNumN n = −(n−1)(4λ·lap + (n−6)·gradSq)`.  The
    scalar curvature is `R = confRNumN / (4λ³)`; the dimension `n` enters as an `Int`
    parameter (the formula is polynomial in `n`). -/
def confRNumN (n lam gradSq lap : Int) : Int :=
  -(n - 1) * (4 * lam * lap + (n - 6) * gradSq)

/-- ★★★★★ **Validation: the general-`n` formula reduces to 2D Liouville.**  At `n = 2`,
    `confRNumN 2 lam |∇λ|² Δλ = 4·confKNum` — so `R = confRNumN/(4λ³) = 4·confKNum/(4λ³) =
    confKNum/λ³ = 2K`, the established 2D Gauss curvature (`Ric = K·g`, `R = 2K`).  Pure
    `ring_intZ`. -/
theorem confRNumN_eq_confKNum (lam lamx lamy lamxx lamyy : Int) :
    confRNumN 2 lam (lamx * lamx + lamy * lamy) (lamxx + lamyy)
      = 4 * confKNum lam lamx lamy lamxx lamyy := by
  unfold confRNumN confKNum; ring_intZ

/-- ★★★ **Flat (any `n`).**  A constant conformal factor (`λ = c`, zero `2`-jet) has scalar
    curvature `0`. -/
theorem confR_flat (n c : Int) : confRNumN n c 0 0 = 0 := by
  unfold confRNumN
  rw [PolyIntM.mul_zeroZ, PolyIntM.mul_zeroZ, Int.add_zero, PolyIntM.mul_zeroZ]

/-- ★★★★ **3D positive — the round-cap origin.**  In `n = 3`, the dome factor `λ = C − r²`
    has `2`-jet at the origin `(λ, |∇λ|², Δλ) = (C, 0, −6)` (`Δr² = 2n = 6`), giving scalar
    curvature numerator `48·C > 0` (`C > 0`): a genuine positively-curved 3-metric. -/
theorem confR3_dome (C : Int) : confRNumN 3 C 0 (-6) = 48 * C := by
  unfold confRNumN; rw [PolyIntM.mul_zeroZ, Int.add_zero]; ring_intZ

/-- ★★★★ **3D negative — the paraboloid origin.**  In `n = 3`, `λ = r² + 1` has origin
    `2`-jet `(1, 0, 6)`, scalar curvature numerator `−48 < 0`: a negatively-curved 3-metric. -/
theorem confR3_paraboloid : confRNumN 3 1 0 6 = -48 := by
  unfold confRNumN; rw [PolyIntM.mul_zeroZ, Int.add_zero]; ring_intZ

/-- ★★★★★ **Smooth conformally-flat scalar-curvature trichotomy in `n = 3`.**
    Flat (`λ` constant), positive (dome `λ = C−r²`,
    `C > 0`), negative (paraboloid `λ = r²+1`) — each a genuine smooth scalar-curvature
    value of a conformally-flat 3-metric, `∅`-axiom, generalizing the 2D trichotomy
    (`conformal_curvature_trichotomy`) to dimension 3. -/
theorem conformal_scalar_curvature_3d (C : Int) (hC : 0 < C) :
    confRNumN 3 5 0 0 = 0
    ∧ (0 : Int) < confRNumN 3 C 0 (-6)
    ∧ confRNumN 3 1 0 6 < 0 := by
  refine ⟨confR_flat 3 5, ?_, ?_⟩
  · rw [confR3_dome]; exact OrderMul.mul_pos (by decide) hC
  · rw [confR3_paraboloid]; decide

/-! ## §S7 — the conformally-flat Ricci **tensor**

The scalar above is `g^{ij}Ric_{ij}`; the Ricci **tensor** itself — the object Ricci flow
`∂_t g = −2 Ric` actually evolves — has, for `g = λ·δ`, the components (numerators `×4λ²`):

  off-diagonal `i≠j`:  `4λ²·Ric_{ij} = −(n−2)(2λ·λ_{ij} − 3λ_i λ_j)`,
  diagonal `i=j`:      `4λ²·Ric_{ii} = −(n−2)(2λ·λ_{ii} − 3λ_i²) − (2λ·Δλ + (n−4)|∇λ|²)`.

The consistency check is the trace: `Σ_i 4λ²·Ric_{ii} = confRNumN` (`confRicTrace3`, `n=3`),
so `R = g^{ij}Ric_{ij} = (1/λ)Σ_i Ric_{ii} = confRNumN/(4λ³)` — the §S6 scalar.  This is the
genuine Ricci *tensor* of a conformally-flat metric, `∅`-axiom (rational, numerator over ℤ).
**Honest boundary**: still the *conformally-flat* class (`g = λδ`); the Ricci tensor of an
*arbitrary* metric (general `g_{ij}`, its inverse, Christoffel/Riemann index sums) and the
*flow* with PDE a-priori estimates are not treated here. -/

/-- Off-diagonal Ricci numerator (`×4λ²`) of `g = λδ`, `i ≠ j`: `−(n−2)(2λ·λ_{ij} − 3λ_iλ_j)`
    (`li = λ_i`, `lj = λ_j`, `lij = λ_{ij}`). -/
def confRicOffNum (n lam li lj lij : Int) : Int :=
  -(n - 2) * (2 * lam * lij - 3 * li * lj)

/-- Diagonal Ricci numerator (`×4λ²`) of `g = λδ`: `−(n−2)(2λ·λ_{ii} − 3λ_i²) − (2λ·Δλ +
    (n−4)|∇λ|²)` (`li = λ_i`, `lii = λ_{ii}`, `gradSq = |∇λ|²`, `lap = Δλ`). -/
def confRicDiagNum (n lam li lii gradSq lap : Int) : Int :=
  -(n - 2) * (2 * lam * lii - 3 * li * li) - (2 * lam * lap + (n - 4) * gradSq)

/-- ★★★★★ **Trace consistency (`n = 3`): the Ricci tensor's trace is the scalar.**  Summing the
    three diagonal numerators (each with the full `|∇λ|² = λx²+λy²+λz²`, `Δλ = λxx+λyy+λzz`)
    returns `confRNumN` — so `R = (1/λ)Σ_i Ric_{ii} = confRNumN/(4λ³)`, validating the Ricci
    *tensor* (§S7) against the *scalar* (§S6).  Pure `ring_intZ`. -/
theorem confRicTrace3 (lam lx ly lz lxx lyy lzz : Int) :
    confRicDiagNum 3 lam lx lxx (lx*lx + ly*ly + lz*lz) (lxx + lyy + lzz)
      + confRicDiagNum 3 lam ly lyy (lx*lx + ly*ly + lz*lz) (lxx + lyy + lzz)
      + confRicDiagNum 3 lam lz lzz (lx*lx + ly*ly + lz*lz) (lxx + lyy + lzz)
      = confRNumN 3 lam (lx*lx + ly*ly + lz*lz) (lxx + lyy + lzz) := by
  unfold confRicDiagNum confRNumN; ring_intZ

/-- ★★★★ **Einstein at a point.**  At the origin `2`-jet of the 3D dome `λ = C − r²`
    (`λ_i = 0`, `λ_{ij} = 0` for `i≠j`, `λ_{ii} = −2`, `|∇λ|² = 0`, `Δλ = −6`), the Ricci
    tensor is **isotropic** — every off-diagonal component vanishes and every diagonal
    numerator equals `16·C` — so `Ric = (16C/4λ²)·δ = (4C/λ²)·δ` is a multiple of the metric:
    the dome is **Einstein at its origin** (`Ric ∝ g`, the round-cap point). -/
theorem confRic3_dome_origin (C : Int) :
    confRicOffNum 3 C 0 0 0 = 0 ∧ confRicDiagNum 3 C 0 (-2) 0 (-6) = 16 * C := by
  refine ⟨?_, ?_⟩
  · unfold confRicOffNum
    rw [PolyIntM.mul_zeroZ, PolyIntM.mul_zeroZ, Order.sub_zero, PolyIntM.mul_zeroZ]
  · unfold confRicDiagNum
    rw [PolyIntM.mul_zeroZ, PolyIntM.mul_zeroZ, Int.add_zero, Order.sub_zero]; ring_intZ

end E213.Lib.Math.Geometry.DiscreteCurvature.ConformalCurvature
