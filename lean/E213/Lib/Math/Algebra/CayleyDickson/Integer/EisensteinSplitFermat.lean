import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFrobeniusConj
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep

/-!
# Fermat in `𝔽_{p'} = ℤ[ω]/(π')` — `z^{p'} ≡ z (mod π')` for a split prime `π'` (∅-axiom)

★★★★★ `split_fermat` : for an Eisenstein prime `π'` of prime norm `‖π'‖² = p'` (so `p' ≡ 1 (mod 3)`
splits as `π'·π̄'`) with `ω ≡ x (mod π')`, **every** `z ∈ ℤ[ω]` satisfies

  `z^{p'} ≡ z   (mod π')`.

`ℤ[ω]/(π') ≅ 𝔽_{p'}` (the residue field has `p'` elements), so this is the field Fermat — the split-prime
analog of `frob_sq_modEq` (`z^{q²} ≡ z` for an inert `q`).

Proof, reusing the residue-field reduction: `reduce_to_int` sends `z ≡ ofInt c (mod π')` with the
rational `c = z.re + z.im·x` (since `ω ≡ x`); `ofInt_fermat` gives `(ofInt c)^{p'} ≡ ofInt c (mod ↑p')`,
which descends to `mod π'` because `π' ∣ ↑p'` (`π'·π̄' = ofInt ‖π'‖² = ofInt p'`, `mul_conj_self`); and
`pow_modEq` cubes `z ≡ ofInt c` to the `p'`-th power.  Chaining: `z^{p'} ≡ (ofInt c)^{p'} ≡ ofInt c ≡ z`.

This is the Frobenius brick for the cubic-reciprocity `π ↔ π'` transfer (the second prime split, not
rational inert).  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitFermat

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq trans symm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (reduce_to_int zdvd_trans)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat (ofInt_fermat)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFrobeniusConj (pow_modEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)

/-- **`ModEq` descends to a divisor of the modulus** — `M' ∣ M`, `a ≡ b (mod M) ⟹ a ≡ b (mod M')`.
    (`ModEq M a b = M ∣ (a + -b)`; transitivity of divisibility.) -/
theorem modEq_descend {M' M a b : ZOmega} (hd : M' ∣ M) (h : ModEq M a b) : ModEq M' a b :=
  zdvd_trans hd h

/-- ★★★★★ **Fermat in `𝔽_{p'} = ℤ[ω]/(π')`** — `z^{p'} ≡ z (mod π')` for a split prime `π'`
    (`‖π'‖² = p'` prime, `ω ≡ x (mod π')`).  The residue field has `p'` elements; the field Fermat.
    ∅-axiom (PURE). -/
theorem split_fermat {π : ZOmega} {p : Nat} {x : Int}
    (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnorm : π.normSq = (p : Int)) (hω : ModEq π Omega (ofInt x))
    (z : ZOmega) : ModEq π (pow z p) z := by
  have hzc : ModEq π z (ofInt (z.re + z.im * x)) := reduce_to_int hω z
  have hdvd : π ∣ ofInt ((p : Nat) : Int) := ⟨conj π, by rw [mul_conj_self π, hnorm]⟩
  have hferm : ModEq (ofInt ((p : Nat) : Int))
      (pow (ofInt (z.re + z.im * x)) p) (ofInt (z.re + z.im * x)) :=
    ofInt_fermat hp hpr (z.re + z.im * x)
  have hferm' : ModEq π (pow (ofInt (z.re + z.im * x)) p) (ofInt (z.re + z.im * x)) :=
    modEq_descend hdvd hferm
  have hzp : ModEq π (pow z p) (pow (ofInt (z.re + z.im * x)) p) := pow_modEq hzc p
  exact trans (trans hzp hferm') (symm hzc)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitFermat
