import E213.Lib.Math.NumberTheory.ModArith.MulOrder
import E213.Lib.Math.NumberTheory.Lcm213
import E213.Lib.Math.NumberTheory.FourSquareSeed

/-!
# OrderPow — the order of a power, `ord(aᵏ) = ord(a) / gcd(ord(a), k)`

Brick 2 of the primitive-root marathon.  First the reusable normalization `ord_mod_eq`
(the order depends only on the base mod `p`), then the order-of-a-power law.

  * `ord_mod_eq` — `ordModP a p = ordModP (a % p) p`.
  * ★★★ `ord_pow` — `ordModP (aᵏ) p = ordModP a p / gcd(ordModP a p, k)` (unit `a`, `k ≥ 1`).

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.OrderPow

open E213.Lib.Math.NumberTheory.ModArith.MulOrder
  (findOrd ordModP pow_ord ord_pos ord_dvd)
open E213.Lib.Math.NumberTheory.Lcm213 (gcd_pos gcd_div_coprime mul_div_cancel_of_dvd)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right dvd_antisymm_213)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc euclid_of_coprime)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §1 — the order depends only on the base mod `p` -/

/-- The search is unchanged by reducing the base mod `p` (`aᵏ ≡ (a%p)ᵏ`). -/
theorem findOrd_mod (a p : Nat) : ∀ (f s : Nat), findOrd a p s f = findOrd (a % p) p s f
  | 0,     _ => rfl
  | f + 1, s => by
    rw [findOrd, findOrd,
        show a ^ s % p = (a % p) ^ s % p from pow_mod_base a p s,
        findOrd_mod a p f (s + 1)]

/-- ★ **`ordModP` depends only on the base mod `p`.** -/
theorem ord_mod_eq (a p : Nat) : ordModP a p = ordModP (a % p) p := by
  show (findOrd a p 1 p).getD 0 = (findOrd (a % p) p 1 p).getD 0
  rw [findOrd_mod a p p 1]

/-! ## §2 — the order of a power -/

/-- `p ∤ aᵏ` for a prime `p` with `p ∤ a` (so `aᵏ % p` is a unit). -/
theorem not_dvd_pow (a p k : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hna : ¬ p ∣ a) : ¬ p ∣ a ^ k := by
  induction k with
  | zero =>
    intro h; rw [Nat.pow_zero] at h
    exact absurd (le_of_dvd_pos p 1 (by decide) h) (Nat.not_le.mpr hp)
  | succ k ih =>
    intro h
    rw [Nat.pow_succ] at h
    exact (nat_prime_dvd_mul p hp hpr (a ^ k) a h).elim ih hna

/-- ★★★ **The order of a power.**  For a unit `a` (`1 ≤ a < p`, `p` prime) and `k ≥ 1`,
    `ordModP (aᵏ) p = ordModP a p / gcd(ordModP a p, k)`. -/
theorem ord_pow (a p k : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) (hk1 : 1 ≤ k) :
    ordModP (a ^ k) p = ordModP a p / gcd213 (ordModP a p) k := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hna : ¬ p ∣ a := fun hpa => absurd (le_of_dvd_pos p a ha0 hpa) (Nat.not_le.mpr halt)
  -- the reduced unit base b = aᵏ % p
  have hnak : ¬ p ∣ a ^ k := not_dvd_pow a p k hp hpr hna
  have hb0 : 0 < a ^ k % p := Nat.pos_of_ne_zero (fun h0 => hnak (dvd_of_mod_eq_zero h0))
  have hblt : a ^ k % p < p := Nat.mod_lt _ hppos
  -- abbreviations
  obtain ⟨o, hodef⟩ : ∃ o, ordModP a p = o := ⟨_, rfl⟩
  have hopos : 0 < o := hodef ▸ ord_pos a p hp hpr ha0 halt
  obtain ⟨g, hgdef⟩ : ∃ g, gcd213 o k = g := ⟨_, rfl⟩
  have hgpos : 0 < g := hgdef ▸ gcd_pos o k hopos
  have hgo : g ∣ o := hgdef ▸ gcd213_dvd_left o k
  have hgk : g ∣ k := hgdef ▸ gcd213_dvd_right o k
  -- opaque gcd-reduced quotients
  obtain ⟨og, hogdef⟩ : ∃ x, o / g = x := ⟨_, rfl⟩
  obtain ⟨kg, hkgdef⟩ : ∃ x, k / g = x := ⟨_, rfl⟩
  have hgoe : g * og = o := by rw [← hogdef]; exact mul_div_cancel_of_dvd g o hgpos hgo
  have hgke : g * kg = k := by rw [← hkgdef]; exact mul_div_cancel_of_dvd g k hgpos hgk
  have hogpos : 0 < og := by
    rcases Nat.eq_zero_or_pos og with h0 | hp'
    · rw [h0, Nat.mul_zero] at hgoe; rw [← hgoe] at hopos; exact absurd hopos (Nat.lt_irrefl 0)
    · exact hp'
  have hcop : gcd213 og kg = 1 := by
    rw [← hogdef, ← hkgdef, ← hgdef]
    exact gcd_div_coprime o k hopos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
  -- key: b^j % p = a^(k·j) % p
  have hbj : ∀ j, (a ^ k % p) ^ j % p = a ^ (k * j) % p := by
    intro j
    rw [← pow_mod_base (a ^ k) p j, ← pow_mul_loc a k j]
  have hao1 : a ^ o % p = 1 := by rw [← hodef]; exact pow_ord a p hp hpr ha0 halt
  -- (1) ord(b) ∣ og:  b^og ≡ a^(k·og) = (a^o)^kg ≡ 1
  have hd1 : ordModP (a ^ k % p) p ∣ og := by
    apply ord_dvd (a ^ k % p) p hp hpr hb0 hblt
    rw [hbj og, show k * og = o * kg from by rw [← hgke, ← hgoe]; ring_nat,
        pow_mul_loc a o kg, pow_mod_base (a ^ o) p kg, hao1, Nat.one_pow]
    exact Nat.mod_eq_of_lt hp
  -- (2) og ∣ ord(b):  b^ord ≡ a^(k·ord) ≡ 1 ⟹ o ∣ k·ord ⟹ og ∣ kg·ord, coprime
  have hd2 : og ∣ ordModP (a ^ k % p) p := by
    obtain ⟨ob, hobdef⟩ : ∃ ob, ordModP (a ^ k % p) p = ob := ⟨_, rfl⟩
    rw [hobdef]
    have hbob : a ^ (k * ob) % p = 1 := by
      rw [← hbj ob, ← hobdef]; exact pow_ord (a ^ k % p) p hp hpr hb0 hblt
    have hodvd : o ∣ (k * ob) := by rw [← hodef]; exact ord_dvd a p hp hpr ha0 halt (k * ob) hbob
    have hred : og ∣ kg * ob := by
      obtain ⟨c, hc⟩ := hodvd
      refine ⟨c, ?_⟩
      have heq : g * (kg * ob) = g * (og * c) := by
        rw [show g * (kg * ob) = (g * kg) * ob from by ring_nat, hgke, hc,
            show o * c = (g * og) * c from by rw [hgoe],
            show (g * og) * c = g * (og * c) from by ring_nat]
      exact Nat.eq_of_mul_eq_mul_left hgpos heq
    rcases Nat.lt_or_ge og 2 with ho2 | ho2
    · have hog1 : og = 1 := Nat.le_antisymm (Nat.le_of_lt_succ ho2) hogpos
      rw [hog1]; exact Nat.one_dvd ob
    · exact euclid_of_coprime kg ob og ho2 ((gcd213_comm og kg) ▸ hcop) hred
  -- assemble + transfer through ord_mod_eq
  have hob_eq : ordModP (a ^ k % p) p = og := dvd_antisymm_213 _ _ hd1 hd2
  rw [ord_mod_eq (a ^ k) p, hob_eq, hodef, hgdef, hogdef]

end E213.Lib.Math.NumberTheory.ModArith.OrderPow
