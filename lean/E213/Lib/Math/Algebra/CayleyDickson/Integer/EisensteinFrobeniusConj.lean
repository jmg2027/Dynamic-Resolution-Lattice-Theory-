import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega

/-!
# The Frobenius `conj z ≡ z^q (mod q)` on `ℤ[ω]/(q) ≅ 𝔽_{q²}` (∅-axiom)

★★★★★ `conj_modEq_pow` : for a prime `q ≡ 2 (mod 3)` (inert in `ℤ[ω]`, so `ℤ[ω]/(q) ≅ 𝔽_{q²}`), the
conjugation **is** the `q`-power Frobenius:

  `z^q ≡ conj z   (mod q)`.

Proof: `z = ofInt z.re + ofInt z.im·ω` (`decomp`); the binary freshman splits `z^q ≡ (ofInt z.re)^q +
(ofInt z.im·ω)^q (mod q)`; `ofInt_fermat` collapses the rational powers `(ofInt a)^q ≡ ofInt a`; and
`ω^q = ω²` (`pow_omega_mod` + `q ≡ 2 mod 3`, exact).  So `z^q ≡ ofInt z.re + ofInt z.im·ω² = conj z`
(the last equality `conj_decomp`, from `conj` being a ring hom with `conj ω = ω²`).

This is the central brick of the cubic-reciprocity finish: it turns `J̄^s` into `J^{qs}`, collapsing the
all-Eisenstein congruence `J^{2s+1}·J̄^s ≡ χ(q)` into the single residue-character power
`J^{(q²−1)/3} ≡ χ(q) (mod q)`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFrobeniusConj

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega conj conj_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
  (ModEq refl trans add_compat mul_left mul_right)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm (conj_add)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (decomp)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFreshman (add_pow_modEq_prime)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (pow_mul_distrib)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega (pow_omega_mod)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat (ofInt_fermat)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow pow_succ one)

/-- `conj (ofInt z) = ofInt z` — conjugation fixes the rational integers (`⟨z,0⟩ ↦ ⟨z−0,−0⟩ = ⟨z,0⟩`). -/
private theorem conj_ofInt (z : Int) : conj (ofInt z) = ofInt z := by
  apply ZOmega.ext
  · show z - 0 = z; rw [Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  · show -(0 : Int) = 0; exact Int.neg_zero

/-- `ω^q = ω²` for `q ≡ 2 (mod 3)` — exact (`pow_omega_mod` reduces the exponent mod 3). -/
private theorem omega_pow_q {q : Nat} (hq3 : q % 3 = 2) : pow Omega q = Omega * Omega := by
  rw [pow_omega_mod q, hq3]; decide

/-- **`conj z = ofInt z.re + ofInt z.im · ω²`** — the conjugate via the `ω`-basis decomposition.  `conj`
    is a ring hom (`conj_add`, `conj_mul`) fixing `ℤ` (`conj_ofInt`) with `conj ω = ω²`. -/
private theorem conj_decomp (z : ZOmega) : conj z = ofInt z.re + ofInt z.im * (Omega * Omega) := by
  rw [show conj z = conj (ofInt z.re + ofInt z.im * Omega) from congrArg conj (decomp z),
      conj_add, conj_mul, conj_ofInt, conj_ofInt, show conj Omega = Omega * Omega from by decide]

/-- ★★★★★ **The Frobenius congruence `z^q ≡ conj z (mod q)`** on `ℤ[ω]/(q)` for a prime `q ≡ 2 (mod 3)`.
    `decomp` + the binary freshman + `ofInt_fermat` + `ω^q = ω²` assemble it.  Conjugation is the
    `q`-power Frobenius (`q` inert).  ∅-axiom (PURE). -/
theorem conj_modEq_pow {q : Nat} (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q) (hq3 : q % 3 = 2)
    (z : ZOmega) : ModEq (ofInt ((q : Nat) : Int)) (pow z q) (conj z) := by
  rw [show pow z q = pow (ofInt z.re + ofInt z.im * Omega) q from
        congrArg (fun w => pow w q) (decomp z),
      conj_decomp z]
  refine trans (add_pow_modEq_prime (ofInt z.re) (ofInt z.im * Omega) q hq hqr) ?_
  refine add_compat (ofInt_fermat hq hqr z.re) ?_
  rw [pow_mul_distrib (ofInt z.im) Omega q, omega_pow_q hq3]
  exact mul_right (ofInt_fermat hq hqr z.im) (Omega * Omega)

/-- ★★★ **`ModEq` respects powering** — `a ≡ b (mod M) ⟹ a^n ≡ b^n (mod M)`.  Induction on `n` via
    `mul_right`/`mul_left`.  ∅-axiom. -/
theorem pow_modEq {M a b : ZOmega} (h : ModEq M a b) :
    ∀ n : Nat, ModEq M (pow a n) (pow b n)
  | 0 => refl M one
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact trans (mul_right (pow_modEq h n) a) (mul_left h (pow b n))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFrobeniusConj
