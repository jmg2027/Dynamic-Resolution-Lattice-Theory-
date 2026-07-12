import E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteLichnerowicz

/-!
# The quadratic character is a K_p Laplacian eigenfunction — p = 5 weld

Bridge 1 of `curvature_spectrum_crossdomain.md`, instantiated at the
atomic dimension `p = d = 5`: the cyclic group of order `p` is one
object read two ways — its **multiplicative** characters are the
number-theory arc's quadratic symbol, its **additive** eigen-data is the
curvature arc's `K_p` Laplacian spectrum.  The weld theorem: the
quadratic character of `ℤ/5` (squares `{1,4}` → `+1`, non-squares
`{2,3}` → `−1`, `0 ↦ 0`), *as a vertex function on `K₅`*, is mean-zero
and hence a full-multiplicity `λ = 5` eigenfunction
(`DiscreteLichnerowicz.km_meanzero_eigen`) — the spectral gap of the
complete graph *is the group order*, and main's character sits inside
branch's eigenspace.

Everything here is finite and `decide`-certified except the eigen step,
which is the general theorem applied — no new primitive, exactly the
"buildable next" of the frontier note.  The general-`p` transport
(orbit-reindexing of `quadratic_orthogonality` from exponent sums to
vertex sums) is the queued M-size follow-up.
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.KpCharacterEigen

open E213.Lib.Math.Combinatorics.IntGridSum (gridSumZ)
open E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteLichnerowicz
  (kmLapG km_meanzero_eigen)

/-- The quadratic character of `ℤ/5` as a vertex function on `K₅`:
    `χ(1) = χ(4) = 1` (the squares), `χ(2) = χ(3) = −1`, `χ(0) = 0`. -/
def chi5 : Nat → Int
  | 1 => 1
  | 4 => 1
  | 2 => -1
  | 3 => -1
  | _ => 0

/-- Character certification, square half: `χ = +1` on every nonzero
    square mod 5 (`1² = 4² = 1`, `2² = 3² = 4`).
    (Stated with `Eq` only — the `Iff`/`∃` form is a propext trap,
    `pure_lean_calibration_synthesis.md`.) -/
theorem chi5_squares : ∀ y, y < 5 → y ≠ 0 → chi5 (y * y % 5) = 1 := by
  decide

/-- Character certification, non-square half: a residue where `χ = −1`
    is hit by no square (`2` and `3` are the non-residues mod 5). -/
theorem chi5_nonsquares :
    ∀ x, x < 5 → chi5 x = -1 → ∀ y, y < 5 → y * y % 5 ≠ x := by
  decide

/-- `chi5` is completely multiplicative on `ℤ/5`:
    `χ(a·b mod 5) = χ(a)·χ(b)` for all residues. -/
theorem chi5_multiplicative :
    ∀ a, a < 5 → ∀ b, b < 5 → chi5 (a * b % 5) = chi5 a * chi5 b := by
  decide

/-- The character is mean-zero over the vertices of `K₅`
    (`0 + 1 − 1 − 1 + 1 = 0` — the order-2 orthogonality, vertex form). -/
theorem chi5_meanzero : gridSumZ 5 chi5 = 0 := by decide

/-- ★★ **The weld** — the quadratic character of `ℤ/5` is a `λ = 5`
    eigenfunction of the `K₅` Laplacian: `L χ = −5·χ` pointwise.
    The spectral gap of the complete graph on the atomic dimension
    `d = 5` is the group order, witnessed by the Legendre character. -/
theorem quadratic_character_is_K5_eigenfunction (x : Nat) :
    kmLapG 5 chi5 x = -((5 : Int) * chi5 x) :=
  km_meanzero_eigen 5 chi5 chi5_meanzero x

/-- ★★ Capstone bundle — character certification + multiplicativity +
    mean-zero + the eigen equation, one conjunction. -/
theorem kp_character_eigen_weld :
    (∀ y, y < 5 → y ≠ 0 → chi5 (y * y % 5) = 1)
    ∧ (∀ x, x < 5 → chi5 x = -1 → ∀ y, y < 5 → y * y % 5 ≠ x)
    ∧ (∀ a, a < 5 → ∀ b, b < 5 → chi5 (a * b % 5) = chi5 a * chi5 b)
    ∧ (gridSumZ 5 chi5 = 0)
    ∧ (∀ x, kmLapG 5 chi5 x = -((5 : Int) * chi5 x)) :=
  ⟨chi5_squares, chi5_nonsquares, chi5_multiplicative, chi5_meanzero,
   quadratic_character_is_K5_eigenfunction⟩

end E213.Lib.Math.Geometry.DiscreteCurvature.KpCharacterEigen
