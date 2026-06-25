import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality

/-!
# The cubic character cubes to one in `ℤ[ω]/(d)` (rung 3b, ∅-axiom)

★★★★ `char_cubes_to_one` : for a norm-`p` Eisenstein prime `d` (`p ≡ 1 mod 3`) and **any** `α ∈ ℤ[ω]`,
the cubic-character power `χ(α) := α^m` (with `m = (p−1)/3`) satisfies

  `χ(α)³ ≡ 1  (mod d)`.

So the character value, read in the residue field `ℤ[ω]/(d) ≅ 𝔽_p`, is a **cube root of unity** —
the first half of "(·/d)₃ takes values in μ₃ = {1, ω, ω²}".  The remaining half (the value is
*exactly* one of the three) is the residue-field root-counting of rung 3c.

## The chain

The power is lifted from rational integers via the residue reduction `ℤ[ω]/(d) = ℤ`-image
(`EisensteinResidue.reduce_to_int`):

  * `pow_cong`   — congruence is preserved by powering: `α ≡ β ⟹ αⁿ ≡ βⁿ`.
  * `ofInt_pow`  — the embedding `ℤ → ℤ[ω]` is a power-hom: `↑a ^ n = ↑(aⁿ)`.
  * `ofInt_pow_modeq_one` — **the residue Fermat lift**: `‖d‖² ∣ aⁿ − 1 ⟹ (↑a)ⁿ ≡ 1 (mod d)`.
  * `pow_add`    — `z^(a+b) = z^a · z^b` (the cube `χ³ = α^(m+m+m)`).

`char_cubes_to_one` chains them: `α ≡ ↑r (mod d)` (reduction), so `α^(3m) ≡ (↑r)^(3m) ≡ ↑(r^(3m)) ≡ 1`
when `‖d‖² ∣ r^(3m) − 1` (rational Fermat in `𝔽_p`, `m = (p−1)/3`, `3m = p−1`).  ∅-axiom throughout.

This continues the cubic-reciprocity ladder: rung 2 built the residue prime `d` and reduction to `ℤ`
(`EisensteinResiduePrime`); this rung shows the half-power is a μ₃-valued character.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
  (ModEq refl trans mul_right mul_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (ofInt_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (modEq_ofInt_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
  (pow one pow_succ pow_zero one_mul mul_one)
open E213.Meta.Algebra213.Ring213 (mul_assoc)

/-- **Powering respects congruence** — `α ≡ β (mod d) ⟹ αⁿ ≡ βⁿ (mod d)` for every `n`.  By induction:
    the `n+1` step is `αⁿ·α ≡ βⁿ·β`, from `mul_right` on the inductive step and `mul_left` on `h`. -/
theorem pow_cong {d α β : ZOmega} (h : ModEq d α β) : ∀ n, ModEq d (pow α n) (pow β n)
  | 0 => refl d one
  | n + 1 => by
      show ModEq d (pow α n * α) (pow β n * β)
      exact trans (mul_right (pow_cong h n) α) (mul_left h (pow β n))

/-- **The `ℤ → ℤ[ω]` embedding is a power-hom** — `(↑a)ⁿ = ↑(aⁿ)`.  By induction using `ofInt_mul`
    (multiplicativity) and `Int.pow_succ`. -/
theorem ofInt_pow (a : Int) : ∀ n, pow (ofInt a) n = ofInt (a ^ n)
  | 0 => rfl
  | n + 1 => by
      show pow (ofInt a) n * ofInt a = ofInt (a ^ (n + 1))
      rw [ofInt_pow a n, ← ofInt_mul, ← Int.pow_succ]

/-- ★★★ **The residue Fermat lift** — if `‖d‖²` divides `aⁿ − 1` in `ℤ`, then the embedded power
    `(↑a)ⁿ ≡ 1 (mod d)` in `ℤ[ω]`.  This is how a rational power-residue fact (`p ∣ aⁿ − 1`, e.g.
    Fermat's little theorem `a^(p−1) ≡ 1`) becomes an Eisenstein congruence: `(↑a)ⁿ = ↑(aⁿ)`, then
    `modEq_ofInt_of_dvd`.  ∅-axiom. -/
theorem ofInt_pow_modeq_one {d : ZOmega} {a : Int} {n : Nat} (h : d.normSq ∣ (a ^ n - 1)) :
    ModEq d (pow (ofInt a) n) (ofInt 1) := by
  rw [ofInt_pow]; exact modEq_ofInt_of_dvd h

/-- **Power additivity** — `z^(a+b) = z^a · z^b`.  By induction on `b`: the base `b = 0` is `mul_one`,
    the step uses `pow_succ` and `mul_assoc`. -/
theorem pow_add (z : ZOmega) (a : Nat) : ∀ b, pow z (a + b) = pow z a * pow z b
  | 0 => by rw [Nat.add_zero]; show pow z a = pow z a * one; rw [mul_one]
  | b + 1 => by
      show pow z (a + b + 1) = pow z a * (pow z b * z)
      rw [pow_succ, pow_add z a b, mul_assoc]

/-- ★★★ **The rational cubic character cubes to one** — for an integer `a` with `‖d‖² ∣ a^(3m) − 1`
    (`3m = m+m+m`), the cube of the half-power `(↑a)^m` is `≡ 1 (mod d)`:

      `(↑a)^m · (↑a)^m · (↑a)^m ≡ 1 (mod d)`.

    `(↑a)^m·(↑a)^m·(↑a)^m = (↑a)^(m+m+m)` (`pow_add`), then `ofInt_pow_modeq_one`.  ∅-axiom. -/
theorem half_pow_cube_one {d : ZOmega} {a : Int} {m : Nat}
    (h : d.normSq ∣ (a ^ (m + m + m) - 1)) :
    ModEq d (pow (ofInt a) m * pow (ofInt a) m * pow (ofInt a) m) (ofInt 1) := by
  have key : pow (ofInt a) (m + m + m) = pow (ofInt a) m * pow (ofInt a) m * pow (ofInt a) m := by
    rw [pow_add, pow_add]
  rw [← key]; exact ofInt_pow_modeq_one h

/-- ★★★★ **The cubic character cubes to one, for any `α ∈ ℤ[ω]`** — given the residue reduction
    `α ≡ ↑r (mod d)` (with `r = α.re + α.im·x` from `reduce_to_int`) and the rational Fermat fact
    `‖d‖² ∣ r^(3m) − 1`, the cube of the half-power `α^m` is `≡ 1 (mod d)`:

      `α^m · α^m · α^m ≡ 1 (mod d)`.

    So `χ(α) := α^m` is a cube root of unity in the residue field — the μ₃-valued half of the cubic
    character.  Chain: `α^(3m) ≡ (↑r)^(3m)` (`pow_cong` on the reduction), `(↑r)^(3m) ≡ ↑1`
    (`ofInt_pow_modeq_one`), and `α^(3m) = α^m·α^m·α^m` (`pow_add`).  ∅-axiom. -/
theorem char_cubes_to_one {d α : ZOmega} {x : Int} {m : Nat}
    (hred : ModEq d α (ofInt (α.re + α.im * x)))
    (h : d.normSq ∣ ((α.re + α.im * x) ^ (m + m + m) - 1)) :
    ModEq d (pow α m * pow α m * pow α m) (ofInt 1) := by
  have key : pow α (m + m + m) = pow α m * pow α m * pow α m := by
    rw [pow_add, pow_add]
  have step1 : ModEq d (pow α (m + m + m)) (pow (ofInt (α.re + α.im * x)) (m + m + m)) :=
    pow_cong hred (m + m + m)
  have step2 : ModEq d (pow (ofInt (α.re + α.im * x)) (m + m + m)) (ofInt 1) :=
    ofInt_pow_modeq_one h
  rw [← key]; exact trans step1 step2

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
