import E213.Lib.Math.NumberSystems.Real213.HyperbolicEllipticTrace
import E213.Meta.Int213.PolyIntMTactic

/-!
# Cayley–Hamilton for `Mat2` — the root of the order-2 dial

The whole order-2 story — the discriminant `disc = tr² − 4·det`, the elliptic/parabolic/hyperbolic
trichotomy, `S² = −I`, `U² = U − I`, `T² = 2T − I`, `G² = 3G − I` — is one identity specialised.
Every `2×2` matrix satisfies its own characteristic equation:

  `M² = tr(M) · M − det(M) · I`   (`cayley_hamilton`).

This is the matrix shadow of the scalar eigen-equation `λ² = tr·λ − det`, whose discriminant is
exactly `tr² − 4·det = disc` (`disc` is *defined* as this — `char_poly_discriminant`).  So:

  - the **dial** `disc = tr² − 4·det` is the discriminant of the Cayley–Hamilton quadratic;
  - each generator's defining relation is `M² = tr·M − det·I` read off its `(tr, det)`: `S` (`0, 1`)
    gives `S² = −I`; `U` (`1, 1`) gives `U² = U − I`; the parabolic `T` (`2, 1`) gives `T² = 2T − I`;
    the golden boost `G` (`3, 1`) gives `G² = 3G − I`.

Cayley–Hamilton, not the trichotomy, is the primitive: the trichotomy is the sign of its
discriminant.  Proved generally (`ring_intZ`), not per matrix.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2CayleyHamilton

open E213.Lib.Math.NumberSystems.Real213.HyperbolicEllipticTrace (Mat2)

/-- The characteristic combination `tr(M) · M − det(M) · I`, written out (the off-diagonal entries of
    `det · I` are `0`, so only the diagonal carries the `det` term). -/
def charComb (m : Mat2) : Mat2 :=
  ⟨Mat2.tr m * m.a - Mat2.det m, Mat2.tr m * m.b, Mat2.tr m * m.c, Mat2.tr m * m.d - Mat2.det m⟩

/-- ★★★★ **Cayley–Hamilton for `Mat2`.**  `M² = tr(M) · M − det(M) · I` (`= charComb M`) — every
    `2×2` matrix satisfies its own characteristic equation.  The single identity behind the whole
    order-2 dial, proved generally by `ring_intZ` (not `decide`). -/
theorem cayley_hamilton (m : Mat2) : Mat2.mul m m = charComb m := by
  rcases m with ⟨a, b, c, d⟩
  have h1 : a * a + b * c = (a + d) * a - (a * d - b * c) := by ring_intZ
  have h2 : a * b + b * d = (a + d) * b := by ring_intZ
  have h3 : c * a + d * c = (a + d) * c := by ring_intZ
  have h4 : c * b + d * d = (a + d) * d - (a * d - b * c) := by ring_intZ
  show Mat2.mk (a * a + b * c) (a * b + b * d) (c * a + d * c) (c * b + d * d)
      = Mat2.mk ((a + d) * a - (a * d - b * c)) ((a + d) * b) ((a + d) * c)
          ((a + d) * d - (a * d - b * c))
  rw [h1, h2, h3, h4]

/-- The discriminant of the Cayley–Hamilton characteristic quadratic `λ² − tr·λ + det` is exactly
    `disc = tr² − 4·det` — the order-2 dial *is* this discriminant. -/
theorem char_poly_discriminant (m : Mat2) :
    Mat2.disc m = Mat2.tr m * Mat2.tr m - 4 * Mat2.det m := rfl

/-- ★★★ **The dial is the Cayley–Hamilton discriminant.**  `M² = tr·M − det·I`, and the sign of its
    discriminant `disc = tr² − 4·det` is the elliptic (`< 0`) / parabolic (`= 0`) / hyperbolic
    (`> 0`) trichotomy.  Cayley–Hamilton is the primitive; the trichotomy is the sign of its
    discriminant. -/
theorem dial_is_char_discriminant (m : Mat2) :
    Mat2.mul m m = charComb m
    ∧ Mat2.disc m = Mat2.tr m * Mat2.tr m - 4 * Mat2.det m :=
  ⟨cayley_hamilton m, char_poly_discriminant m⟩

end E213.Lib.Math.NumberSystems.Real213.Mat2CayleyHamilton
