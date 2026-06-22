import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2SymmetricSpectrum

/-!
# The 2-vertex single-edge graph Laplacian as a concrete `Mat2`

`research-notes/decomposition/practice/graph_theory.md` located a clean ∅-axiom promotion target:
the smallest non-trivial graph Laplacian, the **K₂ Laplacian** `L = D − A = [[1,−1],[−1,1]]`, as a
literal `Mat2`, welding `Mat2SymmetricSpectrum` (the symmetric `q=+1` real-spectrum corner) and
`Mat2Spectrum` (`tr = e₁`, `det = e₂`, the Vieta factorization) to an actual graph.

The K₂ graph is two vertices joined by one edge.  Its degree matrix is `D = [[1,0],[0,1]]` (each
vertex has degree 1) and its adjacency matrix is `A = [[0,1],[1,0]]`, so the **discrete diffusion
operator** is

  `L = D − A = [[1,−1],[−1,1]]`.

Read on a colouring `σ = (x, y)` of the two vertices, `L·σ = (x−y, y−x)` is the per-vertex total
disagreement across the single edge — diffusion's `(Lσ)(v) = Σ_{u∼v}(σ(v) − σ(u))` at `d = 2`.

Everything about it is forced and rational (no `Real213` √-cut needed):

  * `L` is **symmetric** (`b = c = −1`), so `Mat2SymmetricSpectrum.disc_symmetric_nonneg` applies:
    `disc L = (a−d)² + (2b)² = 0 + 4 = 4 ≥ 0` — the spectrum is real, the `q=+1` corner.  The
    diffusion reading cannot go elliptic.
  * `tr L = 2`, `det L = 0`, `disc L = 4`.  `det = 0` puts `0` in the spectrum (the constant fixed
    point); `disc = 4 > 0` (non-scalar, `disc_symmetric_pos_of_nonscalar`) gives two *distinct* real
    eigenvalues.
  * The **spectrum is `{0, 2}`**: `charPoly L λ = (λ − 0)·(λ − 2)`, so via `Mat2Spectrum`,
    `tr L = 0 + 2 = e₁`, `det L = 0 · 2 = e₂`, and `0, 2` are roots of `charPoly L`.
  * `λ₀ = 0` carries the **all-ones / constant eigenvector** `(1,1)`: `L·(1,1) = (0,0) = 0·(1,1)`
    — the diffusion fixed point, the `q=+1` constant, `graph_theory.md`'s δ⁰-kernel made literal.
  * The **Fiedler / algebraic-connectivity value** is `λ₁ = 2 > 0`: `0` is a *simple* eigenvalue
    (`disc > 0`, distinct eigenvalues), so the graph is connected — `dim ker L = 1`.  Here the
    Fiedler value is rational (`√disc = 2`), no `Real213` cut.

This grounds the 2-vertex Laplacian leg of `graph_theory.md`.  The general `n`-vertex (`d × d`)
Laplacian — a constructed `L = D − A` over an arbitrary finite vertex set and its *derived*
spectrum — stays the located open promotion target (the `d > 1` matrix gap shared with
`spectral.md`).

All ∅-axiom (`ring_intZ`; the symmetric-spectrum / Vieta lemmas are the repo's pure ones).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.GraphLaplacian

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum (charPoly)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2SymmetricSpectrum (IsSymmetric)
open E213.Meta.Int213.Order (sub_self_zero)

/-! ## §1 — the K₂ Laplacian as a literal `Mat2` -/

/-- ★★★★ **The 2-vertex single-edge graph Laplacian** `L = D − A = [[1,−1],[−1,1]]` as a concrete
    `Mat2`.  `D = [[1,0],[0,1]]` (both degrees `1`), `A = [[0,1],[1,0]]` (the single edge), so
    `L = D − A`.  The smallest non-trivial graph Laplacian — `graph_theory.md`'s promotion target. -/
def pathLaplacian : Mat2 := ⟨1, -1, -1, 1⟩

/-! ## §2 — the structural facts (symmetric, trace, det, discriminant) -/

/-- The K₂ Laplacian is **symmetric** (`b = c = −1`): `Aᵀ = A` and `D` diagonal force `Lᵀ = L`, so
    `Mat2SymmetricSpectrum` applies and the spectrum is real (`q=+1`). -/
theorem pathLaplacian_symmetric : IsSymmetric pathLaplacian := rfl

/-- `tr L = a + d = 1 + 1 = 2` — the sum of degrees of the two endpoints of the single edge, and
    `= λ₀ + λ₁ = 0 + 2` (`e₁` of the spectrum). -/
theorem pathLaplacian_tr : Mat2.tr pathLaplacian = 2 := rfl

/-- `det L = ad − bc = 1·1 − (−1)(−1) = 0` — the Laplacian is **singular**, so `0` is an eigenvalue:
    the constant / all-ones vector lies in `ker L` (the diffusion fixed point).  `= λ₀ · λ₁ = 0·2`
    (`e₂` of the spectrum). -/
theorem pathLaplacian_det : Mat2.det pathLaplacian = 0 := rfl

/-- ★★★★ **`disc L = 4 ≥ 0`** (the `q=+1` real-spectrum corner).  By the symmetric sum-of-squares
    form `disc = (a−d)² + (2b)² = 0² + (−2)² = 4`.  Via `disc_symmetric_nonneg` this is the concrete
    witness that the K₂ Laplacian's spectrum is real; `disc = 4 > 0` (non-scalar) means two
    *distinct* real eigenvalues.  Here `√disc = 2` is rational — no `Real213` cut. -/
theorem pathLaplacian_disc : Mat2.disc pathLaplacian = 4 := rfl

/-- The K₂ Laplacian's discriminant is non-negative — its spectrum is real, the `q=+1` corner
    (a corollary of `Mat2SymmetricSpectrum.disc_symmetric_nonneg` on `pathLaplacian_symmetric`). -/
theorem pathLaplacian_disc_nonneg : 0 ≤ Mat2.disc pathLaplacian :=
  E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2SymmetricSpectrum.disc_symmetric_nonneg
    pathLaplacian pathLaplacian_symmetric

/-! ## §3 — the spectrum is `{0, 2}` (the Vieta factorization) -/

/-- ★★★★ **The K₂ Laplacian's characteristic polynomial factors as `(λ − 0)·(λ − 2)`.**  So its
    spectrum is `{0, 2}` — `λ₀ = 0` (the constant fixed point) and `λ₁ = 2` (the Fiedler value).
    Pure `ℤ` identity: `charPoly L λ = λ·λ − 2·λ + 0 = (λ − 0)·(λ − 2)`. -/
theorem pathLaplacian_charPoly_factors (lam : Int) :
    charPoly pathLaplacian lam = (lam - 0) * (lam - 2) := by
  show lam * lam - Mat2.tr pathLaplacian * lam + Mat2.det pathLaplacian = (lam - 0) * (lam - 2)
  rw [pathLaplacian_tr, pathLaplacian_det]
  ring_intZ

/-- `tr L = 0 + 2` — the trace is `e₁` of the spectrum `{0, 2}` (`Mat2Spectrum.tr_eq_e1` on the
    factorization). -/
theorem pathLaplacian_tr_eq_e1 : Mat2.tr pathLaplacian = 0 + 2 :=
  E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum.tr_eq_e1
    pathLaplacian 0 2 pathLaplacian_charPoly_factors

/-- `det L = 0 · 2` — the determinant is `e₂` of the spectrum `{0, 2}` (`Mat2Spectrum.det_eq_e2`).
    `det = 0` is exactly "`0` is an eigenvalue", the singular Laplacian's constant kernel. -/
theorem pathLaplacian_det_eq_e2 : Mat2.det pathLaplacian = 0 * 2 :=
  E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum.det_eq_e2
    pathLaplacian 0 2 pathLaplacian_charPoly_factors

/-- ★★★★ **`0` and `2` are the eigenvalues** — both are roots of `charPoly L`
    (`Mat2Spectrum.spectrum_roots` on the factorization): `charPoly L 0 = 0` and
    `charPoly L 2 = 0`.  The spectrum of the K₂ Laplacian is exactly `{0, 2}`. -/
theorem pathLaplacian_spectrum_roots :
    charPoly pathLaplacian 0 = 0 ∧ charPoly pathLaplacian 2 = 0 :=
  E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum.spectrum_roots
    pathLaplacian 0 2 pathLaplacian_charPoly_factors

/-! ## §4 — the constant eigenvector for `λ₀ = 0` (connectivity / the diffusion fixed point) -/

/-- Matrix–vector apply `M·(x,y) = (a·x + b·y, c·x + d·y)` — the `Mat2` acting on a 2-vector
    (a colouring of the two vertices).  Diffusion `L·σ` reads the per-vertex edge disagreement. -/
def apply (M : Mat2) (x y : Int) : Int × Int := (M.a * x + M.b * y, M.c * x + M.d * y)

/-- ★★★★ **The all-ones / constant vector `(1,1)` is in `ker L`** — `L·(1,1) = (0,0)`.  This is the
    `λ₀ = 0` eigenvector: `(1−1, −1+1) = (0,0) = 0·(1,1)`.  The constant colouring is the diffusion
    **fixed point** — nothing disagrees across the single edge — the `q=+1` constant that
    `graph_theory.md` identifies with the δ⁰-kernel (`GraphConnectivity.IsClosed`).  Here it is a
    literal `Mat2` kernel vector. -/
theorem pathLaplacian_const_kernel : apply pathLaplacian 1 1 = (0, 0) := by
  show ((1 : Int) * 1 + (-1) * 1, (-1) * 1 + 1 * 1) = (0, 0)
  rw [show (0 : Int) = 1 - 1 from (sub_self_zero 1).symm]
  refine congr (congrArg Prod.mk ?_) ?_ <;> ring_intZ

/-- `L·(1,1) = 0·(1,1)` — the eigen-equation for `λ₀ = 0` written out: the constant vector is an
    eigenvector with eigenvalue `0`. -/
theorem pathLaplacian_eigen_zero :
    apply pathLaplacian 1 1 = (0 * 1, 0 * 1) := by
  rw [pathLaplacian_const_kernel, E213.Meta.Int213.zero_mul]

/-! ## §5 — the Fiedler / connectivity readout: `λ₁ = 2 > 0` ⟹ connected -/

/-- ★★★★ **The Fiedler value is positive: `λ₁ = 2 > 0` ⟹ the K₂ graph is connected.**  `0` is a
    *simple* eigenvalue: `disc L = 4 > 0` (`disc_symmetric_pos_of_nonscalar`, the Laplacian is
    non-scalar — `b = −1 ≠ 0`) gives two *distinct* real eigenvalues `{0, 2}`, so the kernel is
    1-dimensional (`dim ker L = 1 = #components`) and the second eigenvalue `λ₁ = 2 > 0` is the
    algebraic connectivity.  Stated as `0 < disc` (the strict-hyperbolic / distinct-eigenvalue
    certificate) — `graph_theory.md`'s `connectivity ⟺ λ₁ > 0` at the smallest graph. -/
theorem pathLaplacian_connected : 0 < Mat2.disc pathLaplacian :=
  E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2SymmetricSpectrum.disc_symmetric_pos_of_nonscalar
    pathLaplacian pathLaplacian_symmetric (Or.inr (by decide))

/-- The Fiedler value as a literal: `λ₁ = 2`, and `0 < 2` (positive ⟹ connected).  The rational
    Fiedler value of K₂ — no `Real213` √-cut needed (`√disc = √4 = 2`). -/
theorem pathLaplacian_fiedler_value : (0 : Int) < 2 := by decide

/-! ## §6 — the bundled welded statement -/

/-- ★★★★★ **The 2-vertex single-edge graph Laplacian, fully welded.**  The K₂ Laplacian
    `L = [[1,−1],[−1,1]]` is a concrete `Mat2` with:

      `IsSymmetric L`                  (so the spectrum is real — the `q=+1` corner),
      `tr L = 2`, `det L = 0`, `disc L = 4 ≥ 0`,
      `charPoly L λ = (λ − 0)(λ − 2)`  (the spectrum is `{0, 2}`),
      `0` and `2` are the eigenvalues  (roots of `charPoly L`, with `tr = e₁`, `det = e₂`),
      `L·(1,1) = (0,0)`                (the constant / all-ones vector is the `λ₀ = 0` eigenvector),
      `0 < disc L`                     (the Fiedler value `λ₁ = 2 > 0` — connected, `0` simple).

    This welds `Mat2SymmetricSpectrum` (symmetric real spectrum) and `Mat2Spectrum` (`tr = e₁`,
    `det = e₂`, the Vieta factorization) to a literal graph — grounding `graph_theory.md`'s
    promotion target at the smallest non-trivial graph.  ∅-axiom. -/
theorem pathLaplacian_graph_spectrum :
    IsSymmetric pathLaplacian
    ∧ Mat2.tr pathLaplacian = 2
    ∧ Mat2.det pathLaplacian = 0
    ∧ Mat2.disc pathLaplacian = 4
    ∧ (∀ lam : Int, charPoly pathLaplacian lam = (lam - 0) * (lam - 2))
    ∧ (charPoly pathLaplacian 0 = 0 ∧ charPoly pathLaplacian 2 = 0)
    ∧ apply pathLaplacian 1 1 = (0, 0)
    ∧ 0 < Mat2.disc pathLaplacian :=
  ⟨pathLaplacian_symmetric, pathLaplacian_tr, pathLaplacian_det, pathLaplacian_disc,
   pathLaplacian_charPoly_factors, pathLaplacian_spectrum_roots, pathLaplacian_const_kernel,
   pathLaplacian_connected⟩

end E213.Lib.Math.NumberSystems.Real213.Mat2.GraphLaplacian
