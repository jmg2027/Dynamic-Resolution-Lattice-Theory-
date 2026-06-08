import E213.Lib.Math.NumberTheory.ModArith.EulerConverse

/-!
# EulerFirstSupplement — `−1` is a QR mod `p` ⟺ `p ≡ 1 (mod 4)`

The **first supplement to quadratic reciprocity**, as a clean corollary of Euler's criterion.
With `2m = p−1`: `−1` (the residue `p−1`) is a quadratic residue iff `(p−1)ᵐ ≡ 1 (mod p)`
(`euler_criterion`).  And `(p−1)ᵐ ≡ (−1)ᵐ`, which is `1` when `m` is even and `p−1` when `m` is
odd (`neg_one_sq_mod` / `neg_one_odd_pow_mod`).  So `−1` is a QR iff `m` is even, and `2m = p−1`
makes `m` even ⟺ `p ≡ 1 (mod 4)`.

  * `negone_even_pow` — `(p−1)^(2k) ≡ 1 (mod p)`.
  * `neg_one_pow_dvd_iff_even` — `p ∣ ((p−1)ᵐ − 1) ⟺ m` even.
  * `even_iff_pmod4` — with `2m = p−1`, `m` even ⟺ `p ≡ 1 (mod 4)`.
  * ★★★★★ `neg_one_qr_iff` — `(∃ x, x² ≡ p−1) ⟺ p ≡ 1 (mod 4)`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement

open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (euler_criterion)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
  (pow_mul_loc neg_one_sq_mod neg_one_odd_pow_mod)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
  (dvd_sub_one_of_mod_one mod_one_of_dvd_sub_one one_le_pow')
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.NatHelper (sub_add_cancel add_sub_of_le le_sub_of_add_le add_mul_mod_self_pure)

/-- `m % 2 = 0 ∨ m % 2 = 1` (∅-axiom; core `Nat.mod_two_eq_zero_or_one` is `[propext, Quot.sound]`). -/
private theorem mod_two_cases (m : Nat) : m % 2 = 0 ∨ m % 2 = 1 := by
  rcases Nat.eq_zero_or_pos (m % 2) with h0 | hpos
  · exact Or.inl h0
  · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ (Nat.mod_lt m (by decide))) hpos)

/-- `(p−1)^(2k) ≡ 1 (mod p)`: even powers of `−1` are `1`.  (`(p−1)² ≡ 1`, raised to `k`.) -/
theorem negone_even_pow (e k : Nat) : (e + 1) ^ (2 * k) % (e + 2) = 1 % (e + 2) := by
  rw [pow_mul_loc (e + 1) 2 k, Nat.pow_two, pow_mod_base, neg_one_sq_mod, ← pow_mod_base, Nat.one_pow]

/-- `p ∣ ((p−1)ᵐ − 1) ⟺ m` even.  Odd `m` gives `(p−1)ᵐ ≡ p−1 ≢ 1` (since `p > 2`); even `m`
    gives `(p−1)ᵐ ≡ 1`. -/
theorem neg_one_pow_dvd_iff_even (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) :
    p ∣ ((p - 1) ^ m - 1) ↔ m % 2 = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    have h2p : 2 ≤ p := hp
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le h2p).symm⟩
  show (e + 2) ∣ ((e + 1) ^ m - 1) ↔ m % 2 = 0
  have h2m' : 2 * m = e + 1 := h2m
  have hlt2 : 1 < e + 2 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 e)
  have hge : ∀ k, 1 ≤ (e + 1) ^ k := one_le_pow' (e + 1) (Nat.succ_pos e)
  have hdm := div_add_mod m 2
  constructor
  · intro hd
    rcases mod_two_cases m with hev | hod
    · exact hev
    · exfalso
      have hk : m = 2 * (m / 2) + 1 := by rw [hod] at hdm; exact hdm.symm
      have hpow : (e + 1) ^ m % (e + 2) = e + 1 := by
        rw [hk, neg_one_odd_pow_mod e (m / 2), Nat.mod_eq_of_lt (Nat.lt_succ_self (e + 1))]
      have h1 : (e + 1) ^ m % (e + 2) = 1 :=
        mod_one_of_dvd_sub_one (e + 2) ((e + 1) ^ m) hlt2 (hge m) hd
      rw [hpow] at h1
      have he0 : e = 0 := Nat.succ.inj h1
      rw [he0] at h2m'
      have h2le : 2 ≤ 2 * m := by
        calc 2 = 2 * 1 := by decide
          _ ≤ 2 * m := Nat.mul_le_mul_left 2 hm1
      rw [h2m'] at h2le
      exact absurd h2le (by decide)
  · intro hev
    have hk : m = 2 * (m / 2) := by rw [hev, Nat.add_zero] at hdm; exact hdm.symm
    have h1 : (e + 1) ^ m % (e + 2) = 1 := by
      rw [hk, negone_even_pow e (m / 2), Nat.mod_eq_of_lt hlt2]
    exact dvd_sub_one_of_mod_one (e + 2) ((e + 1) ^ m) h1

/-- With `2m = p−1`: `m` even ⟺ `p ≡ 1 (mod 4)`.  (`p = 2m+1`: `m = 2j ⟹ p = 4j+1`,
    `m = 2j+1 ⟹ p = 4j+3`.) -/
theorem even_iff_pmod4 (p m : Nat) (hp : 1 < p) (h2m : 2 * m = p - 1) :
    m % 2 = 0 ↔ p % 4 = 1 := by
  have hpeq : p = 2 * m + 1 := by
    have h := sub_add_cancel (Nat.le_of_lt hp); rw [← h2m] at h; exact h.symm
  have hdm := div_add_mod m 2
  rcases mod_two_cases m with hev | hod
  · have hk : m = 2 * (m / 2) := by rw [hev, Nat.add_zero] at hdm; exact hdm.symm
    have hp4 : p % 4 = 1 := by
      rw [hpeq, hk, show 2 * (2 * (m / 2)) + 1 = 1 + (m / 2) * 4 from by ring_nat,
          add_mul_mod_self_pure 1 4 (m / 2)]
    exact ⟨fun _ => hp4, fun _ => hev⟩
  · have hk : m = 2 * (m / 2) + 1 := by rw [hod] at hdm; exact hdm.symm
    have hp4 : p % 4 = 3 := by
      rw [hpeq, hk, show 2 * (2 * (m / 2) + 1) + 1 = 3 + (m / 2) * 4 from by ring_nat,
          add_mul_mod_self_pure 3 4 (m / 2)]
    constructor
    · intro h; rw [h] at hod; exact absurd hod (by decide)
    · intro h; rw [hp4] at h; exact absurd h (by decide)

/-- ★★★★★ **First supplement to quadratic reciprocity.**  `−1` (the residue `p−1`) is a quadratic
    residue mod a prime `p` **iff** `p ≡ 1 (mod 4)`.  Euler's criterion (`a = p−1`) + the parity of
    `(−1)ᵐ` + `2m = p−1`. -/
theorem neg_one_qr_iff (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) :
    (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = p - 1) ↔ p % 4 = 1 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  exact (euler_criterion p m (p - 1) hp hpr h2m hm1 (le_sub_of_add_le hp)
      (Nat.sub_lt hppos Nat.zero_lt_one)).symm.trans
    ((neg_one_pow_dvd_iff_even p m hp hpr h2m hm1).trans (even_iff_pmod4 p m hp h2m))

end E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement
