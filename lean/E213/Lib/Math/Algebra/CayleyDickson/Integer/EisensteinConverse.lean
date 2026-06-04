import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit
import E213.Lib.Math.NumberTheory.ModArith.NonFixedExists
import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.ModBezout
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213

/-!
# EisensteinConverse — `p ≡ 1 (mod 3) ⟹ p = a² − ab + b²`

The split converse (sufficient side) of the disc-`−3` Fermat theorem, assembling the two
pillars now both ∅-axiom:

  * **Pillar I** (`∃ x, p ∣ x²+x+1`): from `NonFixedExists.exists_nonfixed` (Lagrange's bound
    gives a non-cube-fixed `a`), FLT (`universal_flt_main`, `a^(p−1) ≡ 1`), and
    `CubeFromFLT.cube_from_nonfixed` (`z = aᵐ − 1` is an order-3 element).
  * **Pillar II** (`p ∣ x²+x+1 ⟹ p = a²−ab+b²`): `EisensteinSplit.split_form` — `ℤ[ω]` is
    norm-Euclidean, so `p` reducible there with norm `p`.

  * `prime_gcd_of_prime` — bridges divisor-dichotomy primality to the Bezout-gcd witness FLT
    needs.
  * ★★★ `cube_root_exists` — `p` prime, `3m = p−1` ⟹ `∃ x : Nat, p ∣ x²+x+1` (Pillar I).
  * ★★★★ `eisenstein_split_converse` — `p` prime, `p % 3 = 1` ⟹ `∃ a b : Int,
    ↑p = a² − ab + b²`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse

open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (exists_nonfixed natCast_mul)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (cube_from_nonfixed)
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_main)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime modBezout_gcd_one)
open E213.Lib.Math.NumberTheory.PolyRoot (nat_dvd_to_int natCast_add)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (split_form)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Tactic.NatHelper (add_sub_cancel_right)

/-- Divisor-dichotomy primality ⟹ the Bezout-gcd witness `(modBezout m p).1 = 1` FLT needs. -/
theorem prime_gcd_of_prime (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ m, 0 < m → m < p → (modBezout m p).1 = 1 := by
  intro m hm0 hmlt
  have hnp : ¬ p ∣ m := by
    intro hpm
    exact absurd (le_of_dvd_pos p m hm0 hpm) (Nat.not_le.mpr hmlt)
  have hco : gcd213 p m = 1 := prime_coprime p m hpr hnp
  have hco' : gcd213 m p = 1 := by rw [gcd213_comm]; exact hco
  exact modBezout_gcd_one m p hco'

/-- ★★★ **Pillar I.**  `p` prime (`hpr`), `3m = p − 1` ⟹ `∃ x : Nat, p ∣ x²+x+1`. -/
theorem cube_root_exists (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hm : 3 * m = p - 1) : ∃ x : Nat, p ∣ (x * x + x + 1) := by
  have hpg := prime_gcd_of_prime p hp hpr
  obtain ⟨a, ha1, halt, hanf⟩ := exists_nonfixed p m hp hpr hm
  have hflt : a ^ (p - 1) % p = 1 := by
    have h := universal_flt_main a p hp ha1 halt hpg
    rw [Nat.mod_eq_of_lt hp] at h
    exact h
  exact cube_from_nonfixed p a m hp hpr ha1 hm hflt hanf

/-- `p % 3 = 1` ⟹ `∃ m, 3m = p − 1`. -/
theorem three_mul_eq_of_mod (p : Nat) (hmod : p % 3 = 1) : ∃ m, 3 * m = p - 1 := by
  refine ⟨p / 3, ?_⟩
  have hdm := div_add_mod p 3
  rw [hmod] at hdm
  -- hdm : 3 * (p / 3) + 1 = p
  generalize p / 3 = q at hdm ⊢
  rw [← hdm, add_sub_cancel_right]

/-- ★★★★ **The Eisenstein split converse.**  `p` prime, `p ≡ 1 (mod 3)` ⟹ `p = a² − ab + b²`
    for some integers `a, b`. -/
theorem eisenstein_split_converse (p : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hmod : p % 3 = 1) :
    ∃ a b : Int, (p : Int) = a * a - a * b + b * b := by
  obtain ⟨m, hm⟩ := three_mul_eq_of_mod p hmod
  obtain ⟨x, hx⟩ := cube_root_exists p m hp hpr hm
  -- transfer the divisibility to ℤ
  have hxcast : ((x * x + x + 1 : Nat) : Int) = (x : Int) * (x : Int) + (x : Int) + 1 := rfl
  have hxint : (p : Int) ∣ ((x : Int) * (x : Int) + (x : Int) + 1) := by
    rw [← hxcast]
    exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact hx)
  -- p ∤ 1 in ℤ
  have hp1 : ¬ ((p : Int) ∣ (1 : Int)) := by
    intro hd
    have hle := le_of_dvd_pos p (Int.natAbs (1 : Int)) (by decide)
      (E213.Lib.Math.NumberTheory.PolyRoot.int_dvd_to_nat p 1 hd)
    rw [show Int.natAbs (1 : Int) = 1 from rfl] at hle
    exact absurd hle (Nat.not_le.mpr hp)
  exact split_form p hp hpr hp1 (x : Int) hxint

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse
