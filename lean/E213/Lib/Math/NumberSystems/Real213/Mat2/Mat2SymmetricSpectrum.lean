import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul

/-!
# Symmetric `Mat2` — the spectrum is real (the `q=+1` corner of the trichotomy)

`Mat2Spectrum` / `spectral.md` left **eigenvalue existence** as the honest residue: for an arbitrary
`Mat2` the characteristic roots `(tr ± √disc)/2` need not be real — the sign of the discriminant
`disc = tr² − 4·det` is the hyperbolic(`>0`, real, `q=+1`)/elliptic(`<0`, complex, `q=−1`) split, and
nothing in `Int` forces `disc ≥ 0`.  The elliptic generators `S, U` (`disc = −4, −3`) are the
escape: their spectrum leaves `ℝ` for `ℂ`.

For the **symmetric** sub-class this residue closes outright — *no* matrix in it goes elliptic.  A
real-symmetric `Mat2` has `b = c`, hence `[[a,b],[b,d]]`, and then

  `disc = tr² − 4·det = (a+d)² − 4(ad − b²) = (a − d)² + 4·b²`,

a **sum of two squares** — a finite `Int` inequality `≥ 0`.  So the symmetric discriminant is
non-negative, the eigenvalues `(tr ± √disc)/2` are real, and the spectrum stays in the `q=+1` corner.
This is the `2×2` spectral theorem: a symmetric operator does not rotate (the elliptic `disc < 0`
escape is structurally unavailable), it scales along real eigendirections.

The squared-gap reading sharpens it further: under the factorization hypothesis
`Mat2Spectrum.disc_eq_gap_squared` gives `disc = (μ−ν)²`; for symmetric `M` that gap-square equals the
sum of squares `(a−d)² + 4b²`, which vanishes **iff** `a = d ∧ b = 0`, i.e. iff `M` is already scalar
(`M = a·I`) — the repeated-eigenvalue cusp.  Off that locus the symmetric spectrum is two *distinct*
real eigenvalues (`disc > 0`, strictly hyperbolic).

What stays a `Real213` residue is only the *value* `√disc` (irrational in general — e.g. the golden
`G` is not symmetric, but a symmetric `[[1,1],[1,0]]` has `disc = 5`, `√5` irrational).  Irrationality
of the eigenvalue *value* is not a gap in the *existence* proof: `disc ≥ 0` is exactly the statement
that the cut `√disc` exists as a `Real213` pointing (a nonneg real has a square root), the
reached-by-none residue, not an escape to `ℂ`.  The honest deliverable here is the **real-spectrum
existence** (`disc ≥ 0`), which is what the spectral theorem asserts; the `Real213` √-cut construction
of the explicit eigenvalues is the orthogonal `Real213` task.

All ∅-axiom (`ring_intZ` + the pure `Int213` order/square lemmas).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2SymmetricSpectrum

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum (charPoly)
open E213.Meta.Int213 (int_sq_nonneg add_nonneg mul_eq_zero)

/-! ## §1 — the symmetric predicate -/

/-- A `Mat2` is **symmetric** when its off-diagonal entries agree, `b = c` (i.e. `M = Mᵀ`).  The
    real-symmetric operators of the `2×2` spectral theorem. -/
def IsSymmetric (M : Mat2) : Prop := M.b = M.c

/-- `Mat2.I`, `Mat2.negI` are symmetric (off-diagonal `0 = 0`). -/
theorem I_isSymmetric : IsSymmetric Mat2.I := rfl
theorem negI_isSymmetric : IsSymmetric Mat2.negI := rfl

/-! ## §2 — the symmetric discriminant is a sum of two squares -/

/-- ★★★★ **The symmetric discriminant is a sum of two squares.**  For `M = [[a,b],[b,d]]`
    (`IsSymmetric`),

      `disc M = tr² − 4·det = (a + d)² − 4(ad − b²) = (a − d)² + 4·b² = (a − d)(a − d) + (2b)(2b)`.

    The off-diagonal `c` is replaced by `b`, so `det = ad − b²` and the cross-term cancels into the
    perfect square `(a − d)²` plus `4b²`.  Pure `ℤ` identity (`ring_intZ`). -/
theorem disc_symmetric_sum_of_squares (M : Mat2) (hsym : IsSymmetric M) :
    Mat2.disc M = (M.a - M.d) * (M.a - M.d) + (2 * M.b) * (2 * M.b) := by
  rcases M with ⟨a, b, c, d⟩
  -- `IsSymmetric` : b = c
  have hbc : b = c := hsym
  show (a + d) * (a + d) - 4 * (a * d - b * c)
      = (a - d) * (a - d) + (2 * b) * (2 * b)
  rw [← hbc]
  ring_intZ

/-- ★★★★ **The symmetric spectrum is real (`disc ≥ 0`, the `q=+1` corner).**  A symmetric `Mat2` has
    non-negative discriminant — the sum of squares `(a−d)² + (2b)² ≥ 0`.  So its eigenvalues
    `(tr ± √disc)/2` are real: a real-symmetric `2×2` operator does **not** go elliptic
    (`disc < 0` is structurally unavailable), it scales along real eigendirections.  This is the
    `2×2` spectral theorem — the eigenvalue-existence residue of `spectral.md`, closed for the
    symmetric case at the existence/`disc≥0` level.  ∅-axiom. -/
theorem disc_symmetric_nonneg (M : Mat2) (hsym : IsSymmetric M) : 0 ≤ Mat2.disc M := by
  rw [disc_symmetric_sum_of_squares M hsym]
  exact add_nonneg (int_sq_nonneg (M.a - M.d)) (int_sq_nonneg (2 * M.b))

/-! ## §3 — the degenerate locus: `disc = 0 ⟺ scalar` (repeated eigenvalue cusp) -/

/-- ★★★ **The symmetric repeated-eigenvalue locus is exactly the scalar matrices.**  For symmetric
    `M`, `disc M = 0` forces `a = d ∧ b = 0`, i.e. `M = a·I` is scalar — the parabolic cusp where the
    two real eigenvalues coincide (`μ = ν`).  Proved by `add_eq_zero_of_nonneg` on the sum of
    squares: both `(a−d)²` and `(2b)²` vanish, hence (no zero divisors) `a = d` and `b = 0`. -/
theorem disc_zero_iff_scalar (M : Mat2) (hsym : IsSymmetric M) (h : Mat2.disc M = 0) :
    M.a = M.d ∧ M.b = 0 := by
  have hsq : (M.a - M.d) * (M.a - M.d) + (2 * M.b) * (2 * M.b) = 0 := by
    rw [← disc_symmetric_sum_of_squares M hsym]; exact h
  obtain ⟨h1, h2⟩ :=
    E213.Meta.Int213.add_eq_zero_of_nonneg (int_sq_nonneg (M.a - M.d)) (int_sq_nonneg (2 * M.b)) hsq
  refine ⟨?_, ?_⟩
  · -- (a − d)² = 0 → a − d = 0 → a = d
    rcases mul_eq_zero h1 with had | had <;>
      exact E213.Meta.Int213.Order.eq_of_sub_eq_zero had
  · -- (2b)² = 0 → 2b = 0 → b = 0
    rcases mul_eq_zero h2 with h2b | h2b <;>
      exact E213.Meta.Int213.OrderMul.eq_zero_of_two_mul_eq_zero h2b

/-- ★★★ **Off the scalar locus the symmetric spectrum is two distinct real eigenvalues.**  If a
    symmetric `M` is non-scalar (`a ≠ d` or `b ≠ 0`), then `disc M > 0` — strictly hyperbolic, the
    two eigenvalues are real and distinct.  Contrapositive of `disc_zero_iff_scalar` over the
    non-negativity `disc ≥ 0`. -/
theorem disc_symmetric_pos_of_nonscalar (M : Mat2) (hsym : IsSymmetric M)
    (hne : M.a ≠ M.d ∨ M.b ≠ 0) : 0 < Mat2.disc M := by
  have hnn : 0 ≤ Mat2.disc M := disc_symmetric_nonneg M hsym
  rcases E213.Meta.Int213.Order.pos_zero_or_neg (Mat2.disc M) with hpos | hzero | hneg
  · exact hpos
  · exfalso
    obtain ⟨had, hb⟩ := disc_zero_iff_scalar M hsym hzero
    rcases hne with hne | hne
    · exact hne had
    · exact hne hb
  · exact absurd hnn (E213.Meta.Int213.Order.not_le_of_lt hneg)

/-! ## §4 — packaging: the symmetric spectrum stays in the `q=+1` corner -/

/-- ★★★★ **The `2×2` symmetric spectral theorem (real spectrum, `q=+1`).**  Bundles the symmetric
    eigenvalue-existence content:

      `disc M = (a−d)² + (2b)²`  (a sum of squares),
      `disc M ≥ 0`               (the spectrum is real — no elliptic escape, the `q=+1` corner),
      `disc M = 0 → a = d ∧ b = 0`  (the repeated eigenvalue ⟺ scalar cusp).

    The eigenvalue-existence residue `spectral.md` flagged — "the general spectrum escapes to ℂ" — is
    **closed for the symmetric case**: a symmetric operator's discriminant is a sum of squares, so
    `disc ≥ 0` and the eigenvalues `(tr ± √disc)/2` are real.  The remaining `Real213` object is only
    the *value* `√disc` (a cut, reached-by-none when irrational), not the *existence* of a real
    spectrum.  ∅-axiom. -/
theorem symmetric_spectrum_real (M : Mat2) (hsym : IsSymmetric M) :
    Mat2.disc M = (M.a - M.d) * (M.a - M.d) + (2 * M.b) * (2 * M.b)
    ∧ 0 ≤ Mat2.disc M
    ∧ (Mat2.disc M = 0 → M.a = M.d ∧ M.b = 0) :=
  ⟨disc_symmetric_sum_of_squares M hsym, disc_symmetric_nonneg M hsym,
   disc_zero_iff_scalar M hsym⟩

/-! ## §5 — under factorization: the symmetric eigenvalue gap is a sum of squares

If the spectrum exists (`hfac`, the factorization hypothesis of `Mat2Spectrum`), the squared
eigenvalue gap `(μ−ν)²` of a symmetric `M` equals the sum of squares `(a−d)² + (2b)²` — and is
therefore `≥ 0`, so `μ, ν` are *real* (a negative gap-square would force a complex pair).  This is the
factorization-level statement of the spectral theorem: the symmetric eigenvalue gap is real. -/

/-- ★★★ **The symmetric eigenvalue gap is a (real, non-negative) sum of squares.**  Under the
    factorization `charPoly M = (λ−μ)(λ−ν)`, the squared gap `(μ−ν)²` of a symmetric `M` equals
    `(a−d)² + (2b)² ≥ 0`.  So the symmetric eigenvalues cannot be a complex-conjugate pair (which
    would need `(μ−ν)² < 0`): the spectrum is real.  Combines `Mat2Spectrum.disc_eq_gap_squared` with
    the sum-of-squares form. -/
theorem symmetric_gap_squared_nonneg (M : Mat2) (hsym : IsSymmetric M) (mu nu : Int)
    (hfac : ∀ lam : Int, charPoly M lam = (lam - mu) * (lam - nu)) :
    (mu - nu) * (mu - nu) = (M.a - M.d) * (M.a - M.d) + (2 * M.b) * (2 * M.b)
    ∧ 0 ≤ (mu - nu) * (mu - nu) := by
  have hgap : Mat2.disc M = (mu - nu) * (mu - nu) :=
    E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum.disc_eq_gap_squared M mu nu hfac
  have hsos : Mat2.disc M = (M.a - M.d) * (M.a - M.d) + (2 * M.b) * (2 * M.b) :=
    disc_symmetric_sum_of_squares M hsym
  refine ⟨?_, ?_⟩
  · rw [← hgap]; exact hsos
  · rw [← hgap]; exact disc_symmetric_nonneg M hsym

end E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2SymmetricSpectrum
