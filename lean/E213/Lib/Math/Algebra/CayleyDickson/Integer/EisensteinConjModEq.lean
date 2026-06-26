import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain

/-!
# `conj` carries a congruence to the conjugate modulus (∅-axiom)

★★★★★ `conj_modEq` : complex conjugation on `ℤ[ω]` is a ring hom, so it preserves congruences — but it
**flips the modulus to its conjugate**:

  `A ≡ B  (mod d)   ⟹   conj A ≡ conj B  (mod conj d)`.

This is the honest form of the "conjugate law" of cubic reciprocity (the source's `χ_π(ᾱ) = conj χ_π(α)`
is a garbled rendering of `χ_{conj d}(conj α) = conj(χ_d(α))`): `conj` does **not** descend to an
automorphism of `ℤ[ω]/(d)` — it maps `ℤ[ω]/(d) → ℤ[ω]/(conj d)`.  Proof: `d ∣ (A + -B)` gives `A + -B =
d·c`; apply the ring-hom `conj` (`conj_mul`, `conj_add`, `conj_neg`) to get `conj A + -(conj B) =
conj d · conj c`, i.e. `conj d ∣ (conj A + -(conj B))`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConjModEq

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (conj conj_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm (conj_add)

/-- `conj (-u) = -(conj u)` in `ℤ[ω]` — `conj` commutes with negation (component-wise, `ring_intZ`). -/
theorem conj_neg (u : ZOmega) : conj (-u) = -(conj u) := by
  refine ZOmega.ext ?_ ?_
  · show (-u.re) - (-u.im) = -(u.re - u.im); ring_intZ
  · show -(-u.im) = -(-u.im); rfl

/-- ★★★★★ **`conj` carries a congruence to the conjugate modulus.**  `A ≡ B (mod d) ⟹ conj A ≡ conj B
    (mod conj d)`.  The honest "conjugate law": `conj` is a ring hom flipping the modulus to `conj d`
    (it maps `ℤ[ω]/(d) → ℤ[ω]/(conj d)`, **not** an automorphism of `ℤ[ω]/(d)`).  ∅-axiom (PURE). -/
theorem conj_modEq {d A B : ZOmega} (h : ModEq d A B) : ModEq (conj d) (conj A) (conj B) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨conj c, by rw [← conj_mul, ← hc, conj_add, conj_neg]⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConjModEq
