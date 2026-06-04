import E213.Lib.Math.Cohomology.Surfaces.P1Squared

/-!
# Hodge Index Theorem on ℙ¹ × ℙ¹ — signature (1, 1)

The product complex surface `ℙ¹ × ℙ¹` has Hodge numbers
`h^{2,0} = 0`, `h^{1,1} = 2`.  Hodge Index Theorem predicts
`signature = (1 + 2·0, 2 − 1) = (1, 1)`.

## Same signature, different Hodge structure (vs T²)

  · **T²** (complex 1-fold, Riemann surface, genus 1):
    `h^{2,0} = h^{0,2} = 1, h^{1,1} = 1` — signature (1, 1) on H¹.

  · **ℙ¹ × ℙ¹** (complex 2-fold, rational surface):
    `h^{2,0} = h^{0,2} = 0, h^{1,1} = 2` — signature (1, 1) on H².

Two **distinct** Kähler 2-folds with same cup-pairing signature
(1, 1) but radically different Hodge diamonds.  The signature is
a *coarser* invariant.

The cup-pairing matrices are *also* identical:
`[[0, 1], [1, 0]]`.  This isomorphism of the abstract bilinear
form shows that the signature alone does not distinguish T²
(elliptic curve) from ℙ¹ × ℙ¹ (rational surface).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexP1Squared

open E213.Lib.Math.Cohomology.Surfaces.P1Squared

/-- ★★★★★ Hodge Index²¹³ on ℙ¹ × ℙ¹ — STRICT ∅-AXIOM.

    Cup-pairing matrix on `H²(ℙ¹×ℙ¹; ℤ)` in the
    `{H₁, H₂}` basis:

        `[[0, 1], [1, 0]]`

    Diagonalised classes:
      · α₊ = H₁ + H₂      →  cup(α₊, α₊) = +2
      · α₋ = H₁ − H₂      →  cup(α₋, α₋) = −2
      · cup(α₊, α₋) = 0    (cup-orthogonal)

    Signature (1, 1) by Sylvester's law of inertia.

    Matches Hodge Index Theorem prediction
    `(1 + 2·h^{2,0}, h^{1,1} − 1) = (1, 1)` for ℙ¹×ℙ¹.

    Same signature as T² but distinct Hodge structure
    (`h^{2,0} = 0` for ℙ¹×ℙ¹ vs `h^{2,0} = 1` for T²). -/
theorem hodge_index_p1_squared_capstone :
    -- Matrix entries
    cup basis_H1 basis_H1 Cell4.vol = 0
    ∧ cup basis_H1 basis_H2 Cell4.vol = 1
    ∧ cup basis_H2 basis_H1 Cell4.vol = 1
    ∧ cup basis_H2 basis_H2 Cell4.vol = 0
    -- Signature (1, 1) witnesses
    ∧ cup alpha_plus alpha_plus Cell4.vol = 2
    ∧ cup alpha_minus alpha_minus Cell4.vol = -2
    ∧ cup alpha_plus alpha_minus Cell4.vol = 0 :=
  ⟨cup_H1H1_zero, cup_H1H2_one, cup_H2H1_one, cup_H2H2_zero,
   cup_alpha_plus, cup_alpha_minus, cup_alpha_ortho⟩

end E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexP1Squared
