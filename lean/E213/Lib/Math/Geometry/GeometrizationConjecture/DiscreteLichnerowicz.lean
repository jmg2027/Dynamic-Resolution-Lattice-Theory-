import E213.Meta.Int213
import E213.Meta.Int213.Bound
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci

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

namespace E213.Lib.Math.Geometry.GeometrizationConjecture.DiscreteLichnerowicz

open E213.Meta.Int213
open E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci (gridSumZ
  gridSumZ_congr gridSumZ_add gridSumZ_sub gridSumZ_mul_left gridSumZ_const)

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

end E213.Lib.Math.Geometry.GeometrizationConjecture.DiscreteLichnerowicz
