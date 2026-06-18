import E213.Meta.Int213
import E213.Meta.Int213.Bound
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Combinatorics.IntGridSum
import E213.Lib.Math.Geometry.DiscreteCurvature.BakryEmeryBipartite

/-!
# Curvature → spectrum: the integrated Bochner / Lichnerowicz bridge (∅-axiom)

The discrete Bakry–Émery curvature `CD(K,∞)` (`BakryEmery.lean`) is a *pointwise*
inequality `Γ₂(f) ≥ K·Γ(f)`.  Summing it over all vertices and using the two
integration-by-parts identities

  `Σ_x Γ₂(f)(x) = Σ_x (Lf(x))²`,   `Σ_x Γ(f)(x) = −Σ_x f(x)·Lf(x)  (= E(f), Dirichlet energy)`

gives the **Lichnerowicz spectral gap**: for a Laplacian eigenfunction `Lf = −λf`,
`λ²·Σf² = Σ(Lf)²  ≥  K·E(f) = K·λ·Σf²`, so `λ ≥ K` — curvature bounds the spectrum.

This file establishes the bridge **exactly** for the complete graph `K_m`, where the
integrated Bochner is not just an inequality but the **identity**

  `Σ_x (Lf(x))² = m · E(f)`      (`km_rayleigh`),

valid for *every* `f` (not only eigenfunctions).  It says the Rayleigh quotient
`Σ(Lf)²/E(f)` is identically `m` on the non-constant space, i.e. the `K_m` Laplacian
`L = J − m·I` satisfies `L² = −m·L` and its only non-zero eigenvalue is `m` (spectrum
`{0, m}`, algebraic connectivity `m`).  Combined with the pointwise
`CD((m+2)/2,∞)` (`cd_complete_graph`) this realizes Lichnerowicz: the spectral gap
`m ≥ (m+2)/2`, the gap exceeding the pointwise curvature bound.

All `∅`-axiom (the identity is pure `gridSumZ` linearity + `ring_intZ`).
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteLichnerowicz

open E213.Meta.Int213
open E213.Lib.Math.Combinatorics.IntGridSum (gridSumZ
  gridSumZ_congr gridSumZ_add gridSumZ_sub gridSumZ_mul_left gridSumZ_const gridSumZ_nonneg)
open E213.Lib.Math.Geometry.DiscreteCurvature.BakryEmeryBipartite (kab_inner)

/-- Global graph Laplacian of `K_m` at vertex `x`: `Lf(x) = Σ_y (f y − f x) = S − m·f x`
    (`S = Σ f`; the `y = x` term vanishes, so the sum is over all `m` vertices). -/
def kmLapG (m : Nat) (f : Nat → Int) (x : Nat) : Int := gridSumZ m f - (m : Int) * f x

/-- `Σ_x (Lf x)² = m²·Σf² − m·S²` (the integrated `|∇²|`/Bochner numerator). -/
theorem km_lap_sq_sum (m : Nat) (f : Nat → Int) :
    gridSumZ m (fun x => kmLapG m f x * kmLapG m f x)
      = (m : Int) * (m : Int) * gridSumZ m (fun x => f x * f x)
        - (m : Int) * (gridSumZ m f * gridSumZ m f) := by
  unfold kmLapG
  rw [show gridSumZ m (fun x => (gridSumZ m f - (m : Int) * f x)
                               * (gridSumZ m f - (m : Int) * f x))
        = gridSumZ m (fun x => gridSumZ m f * gridSumZ m f
            - 2 * ((m : Int) * gridSumZ m f) * f x
            + (m : Int) * (m : Int) * (f x * f x)) from
      gridSumZ_congr m _ _ (fun x _ => by ring_intZ),
      gridSumZ_add, gridSumZ_sub, gridSumZ_const, gridSumZ_mul_left, gridSumZ_mul_left]
  ring_intZ

/-- `Σ_x f x · Lf x = S² − m·Σf²` (so the Dirichlet energy `E(f) = −Σ f·Lf = m·Σf² − S²`). -/
theorem km_f_lap_sum (m : Nat) (f : Nat → Int) :
    gridSumZ m (fun x => f x * kmLapG m f x)
      = gridSumZ m f * gridSumZ m f - (m : Int) * gridSumZ m (fun x => f x * f x) := by
  unfold kmLapG
  rw [show gridSumZ m (fun x => f x * (gridSumZ m f - (m : Int) * f x))
        = gridSumZ m (fun x => gridSumZ m f * f x - (m : Int) * (f x * f x)) from
      gridSumZ_congr m _ _ (fun x _ => by ring_intZ),
      gridSumZ_sub, gridSumZ_mul_left, gridSumZ_mul_left]

/-- Carré du champ (scaled `2Γ`) at vertex `x` of `K_m`: `Σ_y (f y − f x)²`. -/
def twoGammaG (m : Nat) (f : Nat → Int) (x : Nat) : Int :=
  gridSumZ m (fun y => (f y - f x) * (f y - f x))

/-- `Σ_x 2Γ(f)(x) = 2·(m·Σf² − S²)` — the integrated Dirichlet form. -/
theorem km_dirichlet_sum (m : Nat) (f : Nat → Int) :
    gridSumZ m (fun x => twoGammaG m f x)
      = 2 * ((m : Int) * gridSumZ m (fun y => f y * f y) - gridSumZ m f * gridSumZ m f) := by
  rw [show gridSumZ m (fun x => twoGammaG m f x)
        = gridSumZ m (fun x => gridSumZ m (fun y => f y * f y)
            - 2 * gridSumZ m f * f x + (m : Int) * (f x * f x)) from
      gridSumZ_congr m _ _ (fun x _ => by
        unfold twoGammaG; rw [kab_inner m f f x]; ring_intZ),
      gridSumZ_add, gridSumZ_sub, gridSumZ_const, gridSumZ_mul_left, gridSumZ_mul_left]
  ring_intZ

/-- ★★★★ **Green / integration-by-parts identity for `K_m`**: `Σ_x 2Γ(f)(x) =
    −2·Σ_x f x·Lf x`, i.e. the Dirichlet energy `Σ Γ = E(f) = −Σ f·Lf` (the carré du
    champ *is* the Dirichlet form).  With `km_lap_sq_sum` (= `Σ Γ₂ = Σ(Lf)²` up to the
    scale) these are exactly the two integration inputs `lichnerowicz_abstract` consumes
    — closed explicitly for `K_m`. -/
theorem km_green (m : Nat) (f : Nat → Int) :
    gridSumZ m (fun x => twoGammaG m f x)
      = -(2 * gridSumZ m (fun x => f x * kmLapG m f x)) := by
  rw [km_dirichlet_sum, km_f_lap_sum]; ring_intZ

/-- ★★★★★ **The `K_m` Rayleigh / integrated-Bochner identity**:

      `Σ_x (Lf x)² = m · ( −Σ_x f x · Lf x )  = m · E(f)`,

    valid for *every* `f`.  The Rayleigh quotient `Σ(Lf)² / E(f)` is identically `m`:
    the complete-graph Laplacian `L = J − m·I` has spectrum `{0, m}` (algebraic
    connectivity `m`).  This is the **exact** integrated Bochner; with the pointwise
    `cd_complete_graph` (`CD((m+2)/2,∞)`) it gives the Lichnerowicz spectral gap
    `m ≥ (m+2)/2`.  For an eigenfunction `Lf = −λf` (`λ > 0`, `Σf² > 0`):
    `λ²·Σf² = m·λ·Σf²`, hence `λ = m`. -/
theorem km_rayleigh (m : Nat) (f : Nat → Int) :
    gridSumZ m (fun x => kmLapG m f x * kmLapG m f x)
      = (m : Int) * (-(gridSumZ m (fun x => f x * kmLapG m f x))) := by
  rw [km_lap_sq_sum, km_f_lap_sum]; ring_intZ

/-- ★★★★★ **The `K_m` Laplacian spectrum is `{0, m}`.**  For a graph-Laplacian
    eigenfunction `−Lf = λ·f` (i.e. `Lf = −λ·f`), the Rayleigh identity `km_rayleigh`
    forces

      `λ² · Σf² = m · λ · Σf²`,

    so on the non-constant space (`Σf² > 0`) the eigenvalue satisfies `λ² = m·λ`, hence
    `λ ∈ {0, m}` — the complete graph has algebraic connectivity exactly `m` (the unique
    non-zero Laplacian eigenvalue), with multiplicity `m−1`.  This is Lichnerowicz made
    exact: the pointwise `CD((m+2)/2)` lower bound is realized by the genuine gap
    `λ = m ≥ (m+2)/2`. -/
theorem km_eigenvalue (m : Nat) (f : Nat → Int) (lam : Int)
    (heig : ∀ x, x < m → kmLapG m f x = -lam * f x) :
    lam * lam * gridSumZ m (fun x => f x * f x)
      = (m : Int) * lam * gridSumZ m (fun x => f x * f x) := by
  have hL : gridSumZ m (fun x => kmLapG m f x * kmLapG m f x)
          = lam * lam * gridSumZ m (fun x => f x * f x) := by
    rw [show gridSumZ m (fun x => kmLapG m f x * kmLapG m f x)
          = gridSumZ m (fun x => lam * lam * (f x * f x)) from
        gridSumZ_congr m _ _ (fun x hx => by rw [heig x hx]; ring_intZ),
        gridSumZ_mul_left]
  have hR : gridSumZ m (fun x => f x * kmLapG m f x)
          = -lam * gridSumZ m (fun x => f x * f x) := by
    rw [show gridSumZ m (fun x => f x * kmLapG m f x)
          = gridSumZ m (fun x => -lam * (f x * f x)) from
        gridSumZ_congr m _ _ (fun x hx => by rw [heig x hx]; ring_intZ),
        gridSumZ_mul_left]
  have hr := km_rayleigh m f
  rw [hL, hR] at hr
  rw [hr]; ring_intZ

/-! ## §2 — the abstract Lichnerowicz mechanism -/

/-- ★★★★★ **Abstract Lichnerowicz**: from the integrated curvature-dimension bound on a
    Laplacian eigenfunction (`Lf = −λf`, eigenvalue `λ > 0`, `N = Σf² > 0`) — which reads
    `K·(λN) ≤ λ·(λN)` once `Σ(Lf)² = λ²N` and `E(f) = λN` are substituted into
    `Σ(Lf)² ≥ K·E` — the eigenvalue dominates the curvature: `K ≤ λ`.  This is the general
    mechanism; for `K_m` the integration is the *exact* `km_eigenvalue` (`λ = m`), and the
    bridge `Σ Γ₂ = Σ(Lf)²`, `Σ Γ = E` for an arbitrary finite graph is the remaining input
    (recorded in `a6_ricci_core`). -/
theorem lichnerowicz_abstract {K lam N : Int} (hN : 0 < N) (hlam : 0 < lam)
    (hCD : K * (lam * N) ≤ lam * (lam * N)) : K ≤ lam :=
  OrderMul.le_of_mul_le_mul_right_pos hCD (OrderMul.mul_pos hlam hN)

/-! ## §3 — the eigenspaces realized: `{0, m}` with multiplicities `1, m−1` -/

/-- **Mean-zero functions are `λ = m` eigenfunctions.**  If `Σf = 0` then `Lf(x) = −m·f x`
    for every `x` (the centre term `S = 0`).  These are the `(m−1)`-dimensional `λ = m`
    eigenspace (the orthogonal complement of the constants). -/
theorem km_meanzero_eigen (m : Nat) (f : Nat → Int) (h0 : gridSumZ m f = 0) (x : Nat) :
    kmLapG m f x = -((m : Int) * f x) := by
  unfold kmLapG; rw [h0]; exact Order.zero_sub _

/-- **Constant functions are `λ = 0` eigenfunctions** (`Lf ≡ 0`): the `1`-dimensional
    kernel.  With `km_meanzero_eigen` and `km_eigenvalue` this pins the full `K_m`
    Laplacian spectrum `{0¹, m^{m−1}}`. -/
theorem km_const_eigen (m : Nat) (c : Int) (x : Nat) :
    kmLapG m (fun _ => c) x = 0 := by
  unfold kmLapG; rw [gridSumZ_const]; exact Order.sub_self_zero _

/-! ## §4 — gradient-semigroup commutation: the Bochner-with-Ricci coupling on `K_m`

The Bakry–Émery gradient estimate `Γ(P_τ f) ≤ (1 − Kτ)²·Γ(f)` is *the* way curvature
couples to the heat semigroup (the semigroup form of Bochner `½Δ|∇f|² ≥ … + Ric(∇f,∇f)`,
and the engine of the curvature-dependent Li–Yau estimates).  On `K_m` it is **exact**:
one global heat step with self-weight `c` (numerator form, `τ = 1/c`) contracts every
difference by the spectral factor `c − m`, so the carré du champ contracts by `(c − m)²`
pointwise (`km_gradient_contraction`) — and since the gap `m` dominates the Bakry–Émery
curvature `(m+2)/2` (`m ≥ 2`), the contraction beats the curvature rate: the cleared
`CD((m+2)/2,∞)`-rate estimate `4·Γ(P_c u) ≤ (2c−(m+2))²·Γ(u)` (`km_be_gradient_estimate`).
All over ℤ, no division (`τ = 1/c` cleared by the numerator convention). -/

/-- One global heat step on `K_m` with self-weight `c` (numerator of `c·P_{1/c}`):
    `P_c u = c·u + Lu`. -/
def kmStep (m : Nat) (c : Int) (u : Nat → Int) (x : Nat) : Int := c * u x + kmLapG m u x

/-- Differences contract exactly by the spectral factor:
    `P_c u(y) − P_c u(x) = (c − m)·(u(y) − u(x))`. -/
theorem km_step_diff (m : Nat) (c : Int) (u : Nat → Int) (x y : Nat) :
    kmStep m c u y - kmStep m c u x = (c - (m : Int)) * (u y - u x) := by
  unfold kmStep kmLapG
  ring_intZ

/-- `Σ_x Lu(x) = 0` — the global `K_m` Laplacian conserves mass. -/
theorem km_lap_sum_zero (m : Nat) (u : Nat → Int) :
    gridSumZ m (fun x => kmLapG m u x) = 0 := by
  unfold kmLapG
  rw [gridSumZ_sub m (fun _ => gridSumZ m u) (fun x => (m : Int) * u x),
      gridSumZ_const, gridSumZ_mul_left]
  exact Order.sub_self_zero _

/-- Mass under the step: `Σ P_c u = c·Σu` (the `1/c` normalization conserves mass). -/
theorem km_step_mass (m : Nat) (c : Int) (u : Nat → Int) :
    gridSumZ m (fun x => kmStep m c u x) = c * gridSumZ m u := by
  unfold kmStep
  rw [gridSumZ_add m (fun x => c * u x) (fun x => kmLapG m u x),
      gridSumZ_mul_left, km_lap_sum_zero]
  exact Int.add_zero _

/-- The carré du champ is non-negative (a sum of squares). -/
theorem twoGammaG_nonneg (m : Nat) (u : Nat → Int) (x : Nat) :
    0 ≤ twoGammaG m u x :=
  gridSumZ_nonneg m _ (fun _ _ => int_sq_nonneg _)

/-- ★★★★★ **Exact gradient-semigroup commutation on `K_m`**:

      `Γ(P_c u)(x) = (c − m)²·Γ(u)(x)`    (pointwise, every `x`, every `u`).

    The Bakry–Émery commutation `Γ(P_τ f) ≤ e^{−2Kτ}·P_τ Γ(f)` holds on the complete
    graph as an *identity* with the spectral factor `(c − m)²` (`τ = 1/c` numerator
    form): the heat semigroup damps every gradient mode at exactly the gap rate.  This
    is the semigroup face of the Bochner identity — curvature coupled to the flow. -/
theorem km_gradient_contraction (m : Nat) (c : Int) (u : Nat → Int) (x : Nat) :
    twoGammaG m (kmStep m c u) x
      = ((c - (m : Int)) * (c - (m : Int))) * twoGammaG m u x := by
  unfold twoGammaG
  rw [gridSumZ_congr m
        (fun y => (kmStep m c u y - kmStep m c u x) * (kmStep m c u y - kmStep m c u x))
        (fun y => ((c - (m : Int)) * (c - (m : Int))) * ((u y - u x) * (u y - u x)))
        (fun y _ => by
          show (kmStep m c u y - kmStep m c u x) * (kmStep m c u y - kmStep m c u x)
              = ((c - (m : Int)) * (c - (m : Int))) * ((u y - u x) * (u y - u x))
          rw [km_step_diff m c u x y]
          ring_intZ),
      gridSumZ_mul_left]

/-- ★★★★★ **The `CD((m+2)/2,∞)`-rate gradient estimate** (Bochner-with-Ricci, cleared
    `×4`): for `m ≥ 2` and `c ≥ m`,

      `4·Γ(P_c u) ≤ (2c − (m+2))²·Γ(u)`,

    i.e. `Γ(P_τ f) ≤ (1 − Kτ)²·Γ(f)` with the **genuine Bakry–Émery curvature**
    `K = (m+2)/2` (the Lin–Yau-optimal `CD` constant of `K_m`, `cd_complete_graph`) and
    `τ = 1/c`.  The exact contraction rate is the gap `m` (`km_gradient_contraction`),
    and Lichnerowicz (`m ≥ (m+2)/2` for `m ≥ 2`) makes the gap beat the curvature —
    so the curvature constant enters the gradient decay exactly as in the smooth
    Bakry–Émery/Li–Yau theory.  Division-free throughout. -/
theorem km_be_gradient_estimate (m : Nat) (c : Int) (u : Nat → Int) (x : Nat)
    (hm : (2 : Int) ≤ (m : Int)) (hc : (m : Int) ≤ c) :
    4 * twoGammaG m (kmStep m c u) x
      ≤ ((2 * c - ((m : Int) + 2)) * (2 * c - ((m : Int) + 2))) * twoGammaG m u x := by
  rw [km_gradient_contraction m c u x]
  have hG : 0 ≤ twoGammaG m u x := twoGammaG_nonneg m u x
  have h0 : (0 : Int) ≤ c - (m : Int) :=
    Order.le_zero_of_nonneg (Order.sub_nonneg_of_le hc)
  have h1 : (0 : Int) ≤ 2 * (c - (m : Int)) := by
    have h := OrderMul.mul_le_mul_left_nonneg h0 2 (by decide)
    rwa [Int.mul_zero] at h
  have h2 : 2 * (c - (m : Int)) ≤ 2 * c - ((m : Int) + 2) := by
    apply Order.le_of_sub_nonneg
    rw [show 2 * c - ((m : Int) + 2) - 2 * (c - (m : Int)) = (m : Int) - 2 from by
          ring_intZ]
    exact Order.sub_nonneg_of_le hm
  have hsq : (2 * (c - (m : Int))) * (2 * (c - (m : Int)))
      ≤ (2 * c - ((m : Int) + 2)) * (2 * c - ((m : Int) + 2)) :=
    OrderMul.sq_le_sq_of_le h1 h2
  have hfin := OrderMul.mul_le_mul_right_nonneg hsq (twoGammaG m u x) hG
  rw [show 4 * ((c - (m : Int)) * (c - (m : Int)) * twoGammaG m u x)
        = (2 * (c - (m : Int))) * (2 * (c - (m : Int))) * twoGammaG m u x from by
        ring_intZ]
  exact hfin

end E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteLichnerowicz
