import E213.Lib.Math.NumberTheory.ModArith.EulerConverse

/-!
# LegendreMultiplicative — the Legendre character is multiplicative

`a · b` is a quadratic residue mod `p` **iff** (`a` is a QR ⟺ `b` is a QR) — i.e. residue·residue
and nonresidue·nonresidue are residues, residue·nonresidue is a nonresidue.  This is the
multiplicativity `(ab/p) = (a/p)(b/p)` stated without a Legendre-symbol definition.

Via Euler's criterion `QR(c) ⟺ cᵐ ≡ 1 (mod p)` and the dichotomy `cᵐ ≡ ±1`: with
`(ab)ᵐ ≡ aᵐ·bᵐ`, the four sign combinations give exactly the iff.

  * `qr_iff_pow_one` — `QR(a) ⟺ aᵐ ≡ 1 (mod p)`.
  * `pow_m_mod_cases` — `aᵐ % p = 1 ∨ aᵐ % p = p − 1` (a unit's half-power is `±1`).
  * ★★★★★ `legendre_mul` — `QR(a·b) ⟺ (QR(a) ⟺ QR(b))`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative

open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (euler_criterion)
open E213.Lib.Math.NumberTheory.ModArith.EulerCriterion (euler_dichotomy)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pred_mod_of_dvd_succ neg_one_sq_mod)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
  (dvd_sub_one_of_mod_one mod_one_of_dvd_sub_one one_le_pow')
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Tactic.NatHelper (add_sub_of_le)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §0 — local helpers -/

/-- `(a·b)^k = a^k · b^k` (pure). -/
theorem mul_pow_loc (a b : Nat) : ∀ k, (a * b) ^ k = a ^ k * b ^ k
  | 0 => rfl
  | k + 1 => by rw [Nat.pow_succ, mul_pow_loc a b k, Nat.pow_succ, Nat.pow_succ]; ring_nat

/-- `(p−1)² ≡ 1 (mod p)` in `p` form. -/
theorem negone_sq_mod_p (p : Nat) (hp : 1 < p) : ((p - 1) * (p - 1)) % p = 1 % p := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    have h2p : 2 ≤ p := hp
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le h2p).symm⟩
  show ((e + 1) * (e + 1)) % (e + 2) = 1 % (e + 2)
  exact neg_one_sq_mod e

/-- A unit's half-power is `±1`: `aᵐ % p = 1 ∨ aᵐ % p = p − 1`.  (`euler_dichotomy`, read off the
    two divisibility cases.) -/
theorem pow_m_mod_cases (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) :
    a ^ m % p = 1 ∨ a ^ m % p = p - 1 := by
  rcases euler_dichotomy p m a hp hpr h2m ha1 halt with hd | hd
  · exact Or.inl (mod_one_of_dvd_sub_one p (a ^ m) hp (one_le_pow' a ha1 m) hd)
  · right
    obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
      have h2p : 2 ≤ p := hp
      rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le h2p).symm⟩
    exact pred_mod_of_dvd_succ e (a ^ m) hd

/-- **Euler's criterion, residue ⟺ `+1` form.**  `QR(a) ⟺ aᵐ ≡ 1 (mod p)`. -/
theorem qr_iff_pow_one (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a) ↔ a ^ m % p = 1 := by
  refine (euler_criterion p m a hp hpr h2m hm1 ha1 halt).symm.trans ?_
  constructor
  · intro hd; exact mod_one_of_dvd_sub_one p (a ^ m) hp (one_le_pow' a ha1 m) hd
  · intro h; exact dvd_sub_one_of_mod_one p (a ^ m) h

/-! ## §1 — multiplicativity -/

/-- ★★★★★ **The Legendre character is multiplicative.**  For a prime `p`, `2m = p − 1`, units
    `1 ≤ a, b < p`:  `a·b` is a quadratic residue mod `p` **iff** (`a` is a QR ⟺ `b` is a QR).
    Euler's criterion turns each QR into `·ᵐ ≡ 1`; the dichotomy `·ᵐ ≡ ±1` plus
    `(ab)ᵐ ≡ aᵐ·bᵐ` gives the four-case sign rule. -/
theorem legendre_mul (p m a b : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p)
    (hb1 : 1 ≤ b) (hblt : b < p) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = (a * b) % p) ↔
      ((∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a) ↔ (∃ y : Nat, 1 ≤ y ∧ y < p ∧ y ^ 2 % p = b)) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  -- p ∤ a, p ∤ b, p ∤ (a*b) ⟹ (a*b) % p is a unit
  have hnpa : ¬ p ∣ a := fun h => absurd (le_of_dvd_pos p a (Nat.lt_of_lt_of_le Nat.zero_lt_one ha1) h) (Nat.not_le.mpr halt)
  have hnpb : ¬ p ∣ b := fun h => absurd (le_of_dvd_pos p b (Nat.lt_of_lt_of_le Nat.zero_lt_one hb1) h) (Nat.not_le.mpr hblt)
  have hnpab : ¬ p ∣ (a * b) := fun h => (nat_prime_dvd_mul p hp hpr a b h).elim hnpa hnpb
  have hab1 : 1 ≤ (a * b) % p := Nat.pos_of_ne_zero (fun h0 => hnpab (dvd_of_mod_eq_zero h0))
  have hablt : (a * b) % p < p := Nat.mod_lt _ hppos
  -- p − 1 ≠ 1 (p ≥ 3)
  have hp3 : 2 ≤ p - 1 := by
    have : 2 * 1 ≤ 2 * m := Nat.mul_le_mul_left 2 hm1
    rw [h2m] at this; exact this
  have hpne : p - 1 ≠ 1 := fun h => absurd (h ▸ hp3) (by decide)
  have hp1lt : p - 1 < p := Nat.sub_lt hppos Nat.zero_lt_one
  -- the three Euler equivalences
  have hqa := qr_iff_pow_one p m a hp hpr h2m hm1 ha1 halt
  have hqb := qr_iff_pow_one p m b hp hpr h2m hm1 hb1 hblt
  have hqab := qr_iff_pow_one p m ((a * b) % p) hp hpr h2m hm1 hab1 hablt
  have key : ((a * b) % p) ^ m % p = (a ^ m % p * (b ^ m % p)) % p := by
    rw [← pow_mod_base (a * b) p m, mul_pow_loc a b m, mul_mod_pure (a ^ m) (b ^ m) p]
  -- core: (ra·rb) % p = 1 ⟺ (ra = 1 ⟺ rb = 1)
  have core : ((a * b) % p) ^ m % p = 1 ↔ (a ^ m % p = 1 ↔ b ^ m % p = 1) := by
    rw [key]
    rcases pow_m_mod_cases p m a hp hpr h2m ha1 halt with hra | hra <;>
      rcases pow_m_mod_cases p m b hp hpr h2m hb1 hblt with hrb | hrb <;>
      rw [hra, hrb]
    · exact iff_of_true (by rw [Nat.one_mul, Nat.mod_eq_of_lt hp]) Iff.rfl
    · refine iff_of_false ?_ (fun h => hpne (h.mp rfl))
      rw [Nat.one_mul, Nat.mod_eq_of_lt hp1lt]; exact hpne
    · refine iff_of_false ?_ (fun h => hpne (h.mpr rfl))
      rw [Nat.mul_one, Nat.mod_eq_of_lt hp1lt]; exact hpne
    · exact iff_of_true (by rw [negone_sq_mod_p p hp, Nat.mod_eq_of_lt hp]) Iff.rfl
  -- assemble (no rw-with-iff / iff_congr, to stay propext-clean)
  constructor
  · intro hz
    have h1 : a ^ m % p = 1 ↔ b ^ m % p = 1 := core.mp (hqab.mp hz)
    exact ⟨fun ha => hqb.mpr (h1.mp (hqa.mp ha)), fun hb => hqa.mpr (h1.mpr (hqb.mp hb))⟩
  · intro h
    have h1 : a ^ m % p = 1 ↔ b ^ m % p = 1 :=
      ⟨fun hra => hqb.mp (h.mp (hqa.mpr hra)), fun hrb => hqa.mp (h.mpr (hqb.mpr hrb))⟩
    exact hqab.mpr (core.mpr h1)

end E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative
