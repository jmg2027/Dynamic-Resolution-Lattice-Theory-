import E213.Lib.Math.NumberTheory.ModArith.CubicResidue
import E213.Lib.Math.NumberTheory.ModArith.CubeRootsUnityModP
import E213.Meta.Nat.PolyNatMTactic

/-!
# The cubic character as a computable function on `𝔽_p` — `χ(t) = t^m % p` (∅-axiom, Phase A1)

The cubic character on **rational** residues `t ∈ 𝔽_p` (`p ≡ 1 mod 3`, `3m = p − 1`) is the
power-residue map

  `χ(t) := t^m % p`.

By Fermat `χ(t)³ ≡ t^{3m} = t^{p−1} ≡ 1 (mod p)` for a unit `t`, so `χ(t)` is a **cube root of unity
mod `p`** (`cubicChar_cube_one`); the map is multiplicative (`cubicChar_mul`), unit-valued
(`cubicChar_unit`), and trivial exactly on the cubic residues (`cubicChar_one_iff_cube`, restating the
cubic Euler criterion).  This is the rational home of the cubic character — the `t^m`-route value that
the residue-field iso (`EisensteinResidueFieldCubeRoots.cube_roots_rational`) carries into `μ₃ ⊂ ℤ[ω]`,
the first brick of the Jacobi-sum core (Phase A1).  ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CubicCharFp

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (fermat)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc)
open E213.Lib.Math.NumberTheory.ModArith.OrderPow (not_dvd_pow)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle (not_dvd_g)
open E213.Lib.Math.NumberTheory.ModArith.CubicResidue (pow_m_one_iff_cube)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberTheory.ModArith.CubeRootsUnityModP (cube_root_trichotomy)

/-- The cubic character on `𝔽_p`: `χ(t) = t^m % p` (with `m = (p−1)/3`). -/
def cubicChar (p m t : Nat) : Nat := t ^ m % p

/-- **Pure `(s·t)^m = s^m · t^m`** — Nat power distributes over a product.  Induction on `m`. -/
private theorem mul_pow_pure (s t : Nat) : ∀ m, (s * t) ^ m = s ^ m * t ^ m
  | 0 => rfl
  | m + 1 => by
      show (s * t) ^ m * (s * t) = s ^ m * s * (t ^ m * t)
      rw [mul_pow_pure s t m]; ring_nat

/-- ★★★★ **`χ(t)` is a cube root of unity mod `p`** — `χ(t)³ ≡ 1 (mod p)` for a unit `t`.
    `χ(t)³ = (t^m)³ = t^{3m} = t^{p−1} ≡ 1` by Fermat.  The `μ₃`-valued core: every character value
    cubes to one.  ∅-axiom. -/
theorem cubicChar_cube_one (p m t : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h3m : 3 * m = p - 1) (ht1 : 0 < t) (htlt : t < p) :
    cubicChar p m t ^ 3 % p = 1 := by
  show (t ^ m % p) ^ 3 % p = 1
  rw [← pow_mod_base (t ^ m) p 3, ← pow_mul_loc t m 3, Nat.mul_comm m 3, h3m]
  exact fermat t p hp hpr ht1 htlt

/-- **`χ` only sees `t mod p`** — `χ(a % p) = χ(a)`.  `(a%p)^m ≡ a^m (mod p)` (`pow_mod_base`). -/
theorem cubicChar_mod (p m a : Nat) : cubicChar p m (a % p) = cubicChar p m a :=
  (pow_mod_base a p m).symm

/-- ★★★ **The cubic character is multiplicative** — `χ(s·t) ≡ χ(s)·χ(t) (mod p)`.  From `(s·t)^m =
    s^m·t^m` and modular multiplicativity.  ∅-axiom. -/
theorem cubicChar_mul (p m s t : Nat) :
    cubicChar p m (s * t) = (cubicChar p m s * cubicChar p m t) % p := by
  show (s * t) ^ m % p = (s ^ m % p * (t ^ m % p)) % p
  rw [mul_pow_pure s t m]
  exact mul_mod_pure (s ^ m) (t ^ m) p

/-- ★★★ **The character value is a unit** — `0 < χ(t)` for a unit `t`.  If `t^m % p = 0` then `p ∣ t^m`,
    so `p ∣ t` (`p` prime), contradicting `0 < t < p`.  ∅-axiom. -/
theorem cubicChar_unit (p m t : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ht1 : 0 < t) (htlt : t < p) :
    0 < cubicChar p m t := by
  show 0 < t ^ m % p
  rcases Nat.eq_zero_or_pos (t ^ m % p) with h0 | hpos
  · exact absurd (dvd_of_mod_eq_zero h0) (not_dvd_pow t p m hp hpr (not_dvd_g t p ht1 htlt))
  · exact hpos

/-- ★★★★ **The character is trivial exactly on cubic residues** — `χ(t) = 1 ⟺ t` is a cube mod `p`.
    The cubic Euler criterion (`CubicResidue.pow_m_one_iff_cube`) in character form: `χ(t) = t^m % p =
    1` iff `t ≡ x³` for some `x`.  ∅-axiom. -/
theorem cubicChar_one_iff_cube (p m t : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m) (ht1 : 1 ≤ t) (htlt : t < p) :
    cubicChar p m t = 1 ↔ ∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 3 % p = t :=
  pow_m_one_iff_cube p m t hp hpr h3m hm1 ht1 htlt

/-- ★★★★★ **The character is genuinely `μ₃`-valued on `𝔽_p`** — given a rational cube root `x`
    (`p ∣ x²+x+1`), every unit's character value is one of the three cube roots of unity:
    `χ(t) = 1 ∨ χ(t) = x % p ∨ χ(t) = (x·x) % p`.  The cube-root property (`cubicChar_cube_one`) fed
    into the field trichotomy (`CubeRootsUnityModP.cube_root_trichotomy`).  This is the rational image
    of `μ₃` that the residue-field iso carries into `{1, ω, ω²} ⊂ ℤ[ω]`.  ∅-axiom. -/
theorem cubicChar_trichotomy (p m x t : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h3m : 3 * m = p - 1) (hx : p ∣ (x * x + x + 1)) (ht1 : 0 < t) (htlt : t < p) :
    cubicChar p m t = 1 ∨ cubicChar p m t = x % p ∨ cubicChar p m t = (x * x) % p :=
  cube_root_trichotomy p x (cubicChar p m t) hp hpr hx
    (Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)))
    (cubicChar_cube_one p m t hp hpr h3m ht1 htlt)

end E213.Lib.Math.NumberTheory.ModArith.CubicCharFp
