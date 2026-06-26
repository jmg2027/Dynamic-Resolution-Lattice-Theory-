import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega

/-!
# The character power `χ(t)^q = χ̄(t)` for `q ≡ 2 (mod 3)` (∅-axiom)

★★★★ `chiOmega_pow_q` : the **μ₃ Frobenius identity** for the cubic character — for a rational prime
`q ≡ 2 (mod 3)`,

  `χ_ω(t)^q = conj χ_ω(t)`   ( `= χ_ω(t)²`, the `μ₃`-inverse ).

Every character value is in `{0, 1, ω, ω²}`, and on each the `q`-th power (with `q ≡ 2 mod 3`) is the
square: `0^q = 0` (`q≥1`), `1^q = 1`, `ω^q = ω^{q mod 3} = ω²`, `(ω²)^q = ω^{2q} = ω = (ω²)²`.  The
conjugate `conj z = z²` on `μ₃` (`conj_chiOmega_eq_sq`) packages the result as `χ^q = χ̄`.

This is the **number-theory half** of the Gauss-sum Frobenius congruence `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)`:
applied termwise to the first half `g^{⋆q} ≡ Σ_t χ(t)^q·e_{tq%p}` (`gauss_pow_modEq`), it turns the
exponentiated characters into conjugates, leaving the `t ↦ tq%p` reindex as the final step.  ∅-axiom
(PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharPow

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega chiOmega_value)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq (conj_chiOmega_eq_sq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega (pow_omega_mod)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (pow_mul_distrib)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow pow_succ)
open E213.Meta.Algebra213.Ring213 (mul_zero)

/-- `(ofInt 1)^q = ofInt 1` — the identity is fixed by powering (`ofInt 1 = one`). -/
private theorem pow_one_base : ∀ q, pow (ofInt 1) q = ofInt 1
  | 0 => rfl
  | q + 1 => by rw [pow_succ, pow_one_base q]; decide

/-- `0^q = 0` for `q ≥ 1`. -/
private theorem pow_zero_pos : ∀ {q : Nat}, 0 < q → pow (0 : ZOmega) q = 0
  | 0, h => absurd h (by decide)
  | _ + 1, _ => by rw [pow_succ]; exact mul_zero _

/-- ★★★★ **The μ₃ character-power Frobenius** — `χ_ω(t)^q = conj χ_ω(t)` for `q ≡ 2 (mod 3)`.  On each
    of the four character values `{0, 1, ω, ω²}` the `q`-th power equals the square (`conj` on `μ₃`):
    `0^q = 0`, `1^q = 1`, `ω^q = ω^{q%3} = ω²`, `(ω²)^q = ω^q·ω^q = ω²·ω² = ω`.  ∅-axiom (PURE).
     -/
theorem chiOmega_pow_q (p m x t q : Nat) (hq : q % 3 = 2) :
    pow (chiOmega p m x t) q = conj (chiOmega p m x t) := by
  have hq1 : 0 < q := Nat.lt_of_lt_of_le (by decide) (hq ▸ Nat.mod_le q 3)
  rw [conj_chiOmega_eq_sq]
  rcases chiOmega_value p m x t with h | h | h | h <;> rw [h]
  · rw [pow_zero_pos hq1]; decide
  · rw [pow_one_base]; decide
  · rw [pow_omega_mod, hq]; decide
  · rw [pow_mul_distrib, pow_omega_mod, hq]; decide

/-- ★★★★ **The μ₃ character-power for a split prime** — `χ_ω(t)^{p'} = χ_ω(t)` for `p' ≡ 1 (mod 3)`.
    On `{0, 1, ω, ω²}` the `p'`-th power is the **identity** (not the conjugate, as in `chiOmega_pow_q`):
    `0^{p'} = 0`, `1^{p'} = 1`, `ω^{p'} = ω^{p' mod 3} = ω`, `(ω²)^{p'} = ω^{p'}·ω^{p'} = ω·ω = ω²`.  The
    number-theory half of the **split-prime** Gauss-sum Frobenius `g(χ)^{⋆p'} ≡ χ̄(p')·g(χ) (mod π')`
    (`χ(t)^{p'} = χ(t)`, vs the inert `χ(t)^q = χ̄(t)`).  ∅-axiom (PURE). -/
theorem chiOmega_pow_p (p m x t pr : Nat) (hpr : pr % 3 = 1) :
    pow (chiOmega p m x t) pr = chiOmega p m x t := by
  have hp1 : 0 < pr := Nat.lt_of_lt_of_le (by decide) (hpr ▸ Nat.mod_le pr 3)
  rcases chiOmega_value p m x t with h | h | h | h <;> rw [h]
  · rw [pow_zero_pos hp1]
  · rw [pow_one_base]
  · rw [pow_omega_mod, hpr]; decide
  · rw [pow_mul_distrib, pow_omega_mod, hpr]; decide

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharPow
