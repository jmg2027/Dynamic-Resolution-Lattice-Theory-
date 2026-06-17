import E213.Meta.Int213.PolyIntMTactic

/-!
# Stewart's theorem and its corollaries (median length / Apollonius) — ∅-axiom

Stewart's theorem relates the length of a cevian `AD` of a triangle `ABC` (with `D` on `BC`,
`BD : DC = m : n`) to the three side lengths:

> `m · AC² + n · AB² = (m + n) · AD² + m · n · BC²` when `BC = m + n`  (classical form),

equivalently the *scaled* identity `(m+n)·(m·AC² + n·AB²) = (m+n)²·AD² + m·n·BC²` holding for the
cevian foot `D` characterized by the affine (vector) condition `(m+n)·D = n·B + m·C`.

Underneath both lies a **free polynomial identity** in the integer coordinates (no triangle
hypothesis at all) — `stewart_identity` — which `ring_intZ` discharges directly.  The classical
and corollary forms (`stewart_scaled`, the median/Apollonius theorem `apollonius`) follow by
substitution.  Squared distances keep everything in `ℤ`; no `√`, no division.  All ∅-axiom.
-/

namespace E213.Lib.Math.Geometry.StewartTheorem

open E213.Meta.Int213.PolyIntM

/-- A point of the integer plane. -/
abbrev Pt := Int × Int

/-- Squared Euclidean distance between two integer points (stays in `ℤ`). -/
def sq (p q : Pt) : Int := (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)

/-- ★★ **Stewart's free identity** (coordinate / vector form, no triangle hypothesis):
    for integer points `A, B, C` and weights `m, n`, writing the cevian foot in *un-normalized*
    coordinates `F = (n·B + m·C)` and `a = m + n`,

      `a · (m · AC² + n · AB²) = |F − a·A|² + m·n·BC²`,

    where `|F − a·A|² = a²·AD²` once `a·D = F`.  A pure `ring_intZ` polynomial identity. -/
theorem stewart_identity (A B C : Pt) (m n : Int) :
    (m + n) * (m * sq C A + n * sq B A)
      = ((n * B.1 + m * C.1) - (m + n) * A.1) * ((n * B.1 + m * C.1) - (m + n) * A.1)
          + ((n * B.2 + m * C.2) - (m + n) * A.2) * ((n * B.2 + m * C.2) - (m + n) * A.2)
          + m * n * sq C B := by
  show (m + n) * (m * ((C.1 - A.1) * (C.1 - A.1) + (C.2 - A.2) * (C.2 - A.2))
        + n * ((B.1 - A.1) * (B.1 - A.1) + (B.2 - A.2) * (B.2 - A.2)))
      = ((n * B.1 + m * C.1) - (m + n) * A.1) * ((n * B.1 + m * C.1) - (m + n) * A.1)
          + ((n * B.2 + m * C.2) - (m + n) * A.2) * ((n * B.2 + m * C.2) - (m + n) * A.2)
          + m * n * ((C.1 - B.1) * (C.1 - B.1) + (C.2 - B.2) * (C.2 - B.2))
  ring_intZ

/-- ★★★ **Stewart's theorem (scaled, hypothesis-driven)**: if `D` is the cevian foot with
    `(m+n)·D = n·B + m·C` (the affine `BD:DC = m:n` condition, integer-valued), then

      `(m + n) · (m · AC² + n · AB²) = (m + n)² · AD² + m · n · BC²`.

    The classical `m·AC² + n·AB² = (m+n)·(AD² + m·n)` follows after substituting `BC² = (m+n)²`
    and cancelling one factor of `(m+n)`. -/
theorem stewart_scaled (A B C D : Pt) (m n : Int)
    (h1 : (m + n) * D.1 = n * B.1 + m * C.1)
    (h2 : (m + n) * D.2 = n * B.2 + m * C.2) :
    (m + n) * (m * sq C A + n * sq B A)
      = (m + n) * (m + n) * sq A D + m * n * sq C B := by
  rw [stewart_identity A B C m n]
  -- replace `|F − a·A|²` by `a²·AD²` using the foot condition componentwise
  have e1 : (n * B.1 + m * C.1) - (m + n) * A.1 = (m + n) * (D.1 - A.1) := by
    rw [← h1]; ring_intZ
  have e2 : (n * B.2 + m * C.2) - (m + n) * A.2 = (m + n) * (D.2 - A.2) := by
    rw [← h2]; ring_intZ
  rw [e1, e2]
  show ((m + n) * (D.1 - A.1)) * ((m + n) * (D.1 - A.1))
      + ((m + n) * (D.2 - A.2)) * ((m + n) * (D.2 - A.2)) + m * n * sq C B
    = (m + n) * (m + n) * ((A.1 - D.1) * (A.1 - D.1) + (A.2 - D.2) * (A.2 - D.2)) + m * n * sq C B
  show ((m + n) * (D.1 - A.1)) * ((m + n) * (D.1 - A.1))
      + ((m + n) * (D.2 - A.2)) * ((m + n) * (D.2 - A.2))
      + m * n * ((C.1 - B.1) * (C.1 - B.1) + (C.2 - B.2) * (C.2 - B.2))
    = (m + n) * (m + n) * ((A.1 - D.1) * (A.1 - D.1) + (A.2 - D.2) * (A.2 - D.2))
      + m * n * ((C.1 - B.1) * (C.1 - B.1) + (C.2 - B.2) * (C.2 - B.2))
  ring_intZ

/-- ★★★ **Median length / Apollonius' theorem**: for the median to `BC` (`D` its midpoint,
    `2·D = B + C`),

      `AB² + AC² = 2·AD² + ½·BC²`,   in cleared integer form  `2·(AB² + AC²) = 4·AD² + BC²`.

    The `m = n = 1` specialization of Stewart. -/
theorem apollonius (A B C D : Pt)
    (h1 : (2 : Int) * D.1 = B.1 + C.1) (h2 : (2 : Int) * D.2 = B.2 + C.2) :
    (2 : Int) * (sq B A + sq C A) = (4 : Int) * sq A D + sq C B := by
  have hstew := stewart_scaled A B C D 1 1
    (by rw [show (1 : Int) + 1 = 2 by decide, h1]; ring_intZ)
    (by rw [show (1 : Int) + 1 = 2 by decide, h2]; ring_intZ)
  -- (1+1)·(1·AC² + 1·AB²) = (1+1)²·AD² + 1·1·BC²
  show (2 : Int) * (sq B A + sq C A) = (4 : Int) * sq A D + sq C B
  have hL : (2 : Int) * (sq B A + sq C A) = (1 + 1) * (1 * sq C A + 1 * sq B A) := by ring_intZ
  have hR : (4 : Int) * sq A D + sq C B
      = (1 + 1) * (1 + 1) * sq A D + (1 : Int) * 1 * sq C B := by ring_intZ
  rw [hL, hR, hstew]

/-- Smoke: `A=(0,3)`, `B=(0,0)`, `C=(4,0)`, midpoint `D=(2,0)` of `BC`.
    `AB²=9`, `AC²=25`, `AD²=13`, `BC²=16`: `2·(9+25) = 4·13 + 16 = 68`. -/
theorem apollonius_smoke :
    (2 : Int) * (sq (0, 0) (0, 3) + sq (4, 0) (0, 3))
      = (4 : Int) * sq (0, 3) (2, 0) + sq (4, 0) (0, 0) := by decide

end E213.Lib.Math.Geometry.StewartTheorem
