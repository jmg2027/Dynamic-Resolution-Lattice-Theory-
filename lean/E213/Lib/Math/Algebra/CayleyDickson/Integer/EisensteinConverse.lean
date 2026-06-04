import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit
import E213.Lib.Math.NumberTheory.ModArith.NonFixedExists
import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.ModBezout
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
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

**Necessity + iff.**  The disc-`−3` form's χ₋₃ obstruction over `ℤ`:

  * `sq_mod3` / `form_mod3` — `a²−ab+b² ≡ 0` or `1 (mod 3)`, never `2`, via
    `4(a²−ab+b²) = (2a−b)² + 3b²` (the form's residue is a square's residue).
  * `mod_one_of_form` — a prime `p ≠ 3` of the form `a²−ab+b²` has `p ≡ 1 (mod 3)`.
  * ★★★★★ `eisenstein_iff` — for a prime `p ≠ 3`:
    `p ≡ 1 (mod 3) ⟺ ∃ a b : Int, ↑p = a² − ab + b²`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse

open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (exists_nonfixed natCast_mul natCast_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (cube_from_nonfixed mod_one_of_dvd_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_main)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime modBezout_gcd_one)
open E213.Lib.Math.NumberTheory.PolyRoot (nat_dvd_to_int int_dvd_to_nat natCast_add dvd_add')
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (split_form)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213 cases_lt_two)
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

/-! ## Necessity (the χ₋₃ obstruction over `ℤ`) and the full iff -/

/-- `2·|r| ≤ 3` ⟹ `r ∈ {−1, 0, 1}` (balanced residues mod 3). -/
theorem int_small (r : Int) (h : 2 * r.natAbs ≤ 3) : r = -1 ∨ r = 0 ∨ r = 1 := by
  have hle : r.natAbs ≤ 1 := by
    rcases Nat.lt_or_ge r.natAbs 2 with hlt | hge
    · exact Nat.le_of_lt_succ hlt
    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 2 hge) h) (by decide)
  rcases Int.natAbs_eq r with he | he
  · rcases cases_lt_two (Nat.lt_succ_of_le hle) with h0 | h1
    · right; left; rw [he, h0]; rfl
    · right; right; rw [he, h1]; rfl
  · rcases cases_lt_two (Nat.lt_succ_of_le hle) with h0 | h1
    · right; left; rw [he, h0]; decide
    · left; rw [he, h1]; decide

/-- A perfect square is `≡ 0` or `1 (mod 3)`: `3 ∣ c²` or `3 ∣ (c² − 1)`. -/
theorem sq_mod3 (c : Int) : (3 : Int) ∣ (c * c) ∨ (3 : Int) ∣ (c * c - 1) := by
  obtain ⟨q, r, hd, hr⟩ := centered_div_int c 3 (by decide)
  rw [show (3 : Int).natAbs = 3 from rfl] at hr
  have hpack : (3 : Int) ∣ (c * c - r * r) := ⟨3 * q * q + 2 * q * r, by rw [hd]; ring_intZ⟩
  rcases int_small r hr with h | h | h
  · right
    have e : c * c - r * r = c * c - 1 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack
  · left
    have e : c * c - r * r = c * c := by rw [h, show (0 : Int) * 0 = 0 from rfl,
      E213.Meta.Int213.Order.sub_zero]
    rw [e] at hpack; exact hpack
  · right
    have e : c * c - r * r = c * c - 1 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack

/-- ★★★ **The χ₋₃ obstruction over `ℤ`.**  `a² − ab + b² ≡ 0` or `1 (mod 3)` — never `2` —
    via `4(a²−ab+b²) = (2a−b)² + 3b²` (so the form's residue is a square's residue). -/
theorem form_mod3 (a b : Int) :
    (3 : Int) ∣ (a * a - a * b + b * b) ∨ (3 : Int) ∣ (a * a - a * b + b * b - 1) := by
  have key : (3 : Int) ∣ ((a * a - a * b + b * b) - (2 * a - b) * (2 * a - b)) :=
    ⟨a * b - a * a, by ring_intZ⟩
  rcases sq_mod3 (2 * a - b) with h | h
  · left
    have e : (a * a - a * b + b * b)
        = ((a * a - a * b + b * b) - (2 * a - b) * (2 * a - b)) + (2 * a - b) * (2 * a - b) := by
      ring_intZ
    rw [e]; exact dvd_add' key h
  · right
    have e : (a * a - a * b + b * b - 1)
        = ((a * a - a * b + b * b) - (2 * a - b) * (2 * a - b))
          + ((2 * a - b) * (2 * a - b) - 1) := by ring_intZ
    rw [e]; exact dvd_add' key h

/-- ★★★★ **Necessity.**  `p` prime, `p ≠ 3`, `p = a² − ab + b²` ⟹ `p ≡ 1 (mod 3)`.  The form
    avoids `2 mod 3` (`form_mod3`); a prime `≠ 3` avoids `0 mod 3`; so `1` remains. -/
theorem mod_one_of_form (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hne : p ≠ 3) (a b : Int) (hrep : (p : Int) = a * a - a * b + b * b) : p % 3 = 1 := by
  have h3np : ¬ (3 ∣ p) := by
    intro hd
    rcases hpr 3 hd with h | h
    · exact absurd h (by decide)
    · exact hne h.symm
  rcases form_mod3 a b with hdiv | hdiv
  · -- 3 ∣ ↑p ⟹ 3 ∣ p, contradiction
    rw [← hrep] at hdiv
    exact absurd (by rw [← Int.natAbs_ofNat p]; exact int_dvd_to_nat 3 (p : Int) hdiv) h3np
  · -- 3 ∣ (↑p − 1) = ↑(p − 1) ⟹ 3 ∣ (p − 1) ⟹ p % 3 = 1
    rw [← hrep, ← natCast_sub_one p (Nat.le_of_lt hp)] at hdiv
    have hnat : 3 ∣ (p - 1) := by
      rw [← Int.natAbs_ofNat (p - 1)]; exact int_dvd_to_nat 3 ((p - 1 : Nat) : Int) hdiv
    exact mod_one_of_dvd_sub_one 3 p (by decide) (Nat.le_of_lt hp) hnat

/-- ★★★★★ **The Eisenstein split iff.**  For a prime `p ≠ 3`:
    `p ≡ 1 (mod 3) ⟺ ∃ a b : Int, ↑p = a² − ab + b²`.  Both directions ∅-axiom. -/
theorem eisenstein_iff (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hne : p ≠ 3) :
    p % 3 = 1 ↔ ∃ a b : Int, (p : Int) = a * a - a * b + b * b := by
  constructor
  · intro hmod; exact eisenstein_split_converse p hp hpr hmod
  · rintro ⟨a, b, hrep⟩; exact mod_one_of_form p hp hpr hne a b hrep

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse
