import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature
import E213.Meta.Int213.PolyIntMTactic

/-!
# EisensteinEuclidean — the covering-radius bound (`ℤ[ω]` is norm-Euclidean)

`EisensteinClassNumber` shows disc `−3` has class number one at the level of *forms*.  Its
ring-theoretic source is that `ℤ[ω]` is a **Euclidean domain** (for the norm), hence a PID —
the structural fact behind the split-prime descent `p ≡ 1 (mod 3) ⟹ p = N(π)` that
`EisensteinSplitting` records witnesses for.

The geometric heart of norm-Euclideanness is the **covering radius** of the Eisenstein
lattice: every point of `ℂ` is within `ℓ²`-norm `< 1` of a lattice point of `ℤ[ω]`.  The
Euclidean step `α = βγ + ρ` chooses `γ` as the nearest lattice point to `α/β`; the centered
remainders `(r₁, r₂)` of the coordinates satisfy `2|rᵢ| ≤ N` (`N = ‖β‖²`), and the bound
below gives `‖ρ‖² · N = r₁² − r₁r₂ + r₂² ≤ (3/4)N² < N²`, so `‖ρ‖² < ‖β‖²` — the descent
terminates.

  * ★★★ `covering_bound` — for all integers with `4x² ≤ N²` and `4y² ≤ N²` (i.e.
    `2|x| ≤ N`, `2|y| ≤ N`), the Eisenstein form is bounded: `8(x² − xy + y²) ≤ 6N²`.
    Equivalently the covering radius² is `≤ 3/4 < 1`.  Proved `∅`-axiom by the
    sum-of-nonnegatives identity `6N² − 8(x²−xy+y²) = 3(N²−4x²) + 3(N²−4y²) + (2x+2y)²`.

**The wall (honest scope).**  This is the covering-radius *inequality* — the geometric
content.  Assembling the full Euclidean algorithm (the existence of centered remainders via
integer division, then `‖ρ‖² < ‖β‖²`, then `gcd` / unique factorization, then the
descent `p ≡ 1 mod 3 ⟹ p = N(π)`) plus the quadratic-residue input (`−3` is a QR mod `p`
iff `p ≡ 1 mod 3`, which needs an order-3 element of `(ℤ/p)ˣ`) is the remaining multi-step
work; the split converse and the period value stay open as recorded.  What is pinned here
is the load-bearing inequality: the Eisenstein lattice's covering radius is `< 1`, the
reason `ℤ[ω]` is Euclidean.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinEuclidean

open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature (sq_nonneg)
open E213.Meta.Int213 (add_nonneg mul_nonneg)
open E213.Meta.Int213.Order
  (sub_nonneg_of_le le_zero_of_nonneg nonneg_of_le_zero le_of_sub_nonneg)

/-- ★★★ **The Eisenstein covering-radius bound.**  If `4x² ≤ N²` and `4y² ≤ N²` (the
    centered-remainder condition `2|x| ≤ N`, `2|y| ≤ N`), then `8(x² − xy + y²) ≤ 6N²` —
    the Eisenstein form is at most `(3/4)N²`, so the lattice covering radius² is `≤ 3/4 < 1`.
    This is why `ℤ[ω]` is norm-Euclidean: the remainder always has strictly smaller norm.
    Proved by the sum-of-nonnegatives identity
    `6N² − 8(x²−xy+y²) = 3(N²−4x²) + 3(N²−4y²) + (2x+2y)²`. -/
theorem covering_bound (x y N : Int) (hx : 4 * x * x ≤ N * N) (hy : 4 * y * y ≤ N * N) :
    8 * (x * x - x * y + y * y) ≤ 6 * (N * N) := by
  have hP : (0 : Int) ≤ N * N - 4 * x * x := le_zero_of_nonneg (sub_nonneg_of_le hx)
  have hQ : (0 : Int) ≤ N * N - 4 * y * y := le_zero_of_nonneg (sub_nonneg_of_le hy)
  have hid : 6 * (N * N) - 8 * (x * x - x * y + y * y)
      = 3 * (N * N - 4 * x * x) + 3 * (N * N - 4 * y * y)
        + (2 * x + 2 * y) * (2 * x + 2 * y) := by ring_intZ
  have hnn : (0 : Int) ≤ 6 * (N * N) - 8 * (x * x - x * y + y * y) := by
    rw [hid]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by decide) hP) (mul_nonneg (by decide) hQ))
      (sq_nonneg (2 * x + 2 * y))
  exact le_of_sub_nonneg (nonneg_of_le_zero hnn)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinEuclidean
