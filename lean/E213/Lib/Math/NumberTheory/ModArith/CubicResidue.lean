import E213.Lib.Math.NumberTheory.ModArith.DiscreteLogParity
import E213.Meta.Nat.ModPow213
import E213.Meta.Nat.AddMod213

/-!
# Cubic residues — the cubic character is the discrete-log mod-3 class (∅-axiom)

The cubic analogue of `DiscreteLogParity` (which read the **quadratic** character as the discrete-log
*parity*).  For a prime `p ≡ 1 (mod 3)` — encoded as `3·m = p − 1` — the unit group `(ℤ/pℤ)*` is
cyclic of order `3m`, so cubing is a 3-to-1 map onto the index-3 subgroup of cubes.  Hence a power
`g^k` of a primitive root `g` **is a cube iff `3 ∣ k`**, and the cubic character of any unit is the
mod-3 class of its discrete logarithm.

* `cube_pow_iff_three_dvd_exp` — `g^k` is a cube mod `p` ⟺ `3 ∣ k`;
* `cube_iff_three_dvd_dlog` — per unit `a`: there is a primitive root `g` and a discrete log `k`
  (`a ≡ g^k`) with `a` a cube ⟺ `3 ∣ k`.

This is the **foundation of cubic-residue theory** and the entry point toward cubic (Eisenstein)
reciprocity — the law itself lives over the Eisenstein integers `ℤ[ω]` (`CayleyDickson/Integer/`,
the Euclidean-domain machinery), with the rational cubic character `(·/π)₃` reading back to this
mod-`p` characterisation.  Proof mirrors `qr_pow_iff_even_exp`: the cube-root satisfies `a^m ≡ 1` by
Fermat, which the order chain (`pow_one_iff_ord_dvd` + `three_mul_dvd_iff`) turns into `3 ∣ k`; the
converse exhibits `g^{k/3}` as the root.  ∅-axiom throughout.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CubicResidue

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP fermat)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc)
open E213.Lib.Math.NumberTheory.ModArith.OrderPow (not_dvd_pow)
open E213.Lib.Math.NumberTheory.ModArith.DiscreteLogParity (pow_one_iff_ord_dvd dlog_exists)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle (not_dvd_g)
open E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot (exists_primitive_root)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)

/-- `3m ∣ km ⟺ 3 ∣ k` (cancel the positive `m`) — the third-order divisibility collapses to the
    mod-3 class of the exponent.  The cubic analogue of `DiscreteLogParity.two_mul_dvd_iff`. -/
theorem three_mul_dvd_iff (m k : Nat) (hm : 0 < m) : 3 * m ∣ k * m ↔ 3 ∣ k := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := h
    have e : m * k = m * (3 * d) := by rw [Nat.mul_comm m k, hd]; ring_nat
    exact ⟨d, Nat.eq_of_mul_eq_mul_left hm e⟩
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hc]; ring_nat⟩

/-- ★★★★★ **The cubic character is the discrete-log mod-3 class.**  For a prime `p` (`3m = p − 1`,
    i.e. `p ≡ 1 mod 3`) and a primitive root `g` (`ordModP g p = p − 1`):

      `g^k` is a cubic residue mod `p`  ⟺  `3 ∣ k`.

    `⟹`: a cube root `x` of `g^k` has `(g^k)^m ≡ x^{3m} = x^{p−1} ≡ 1` (Fermat), so the order `p−1 =
    3m` divides `km`, forcing `3 ∣ k` (`three_mul_dvd_iff`).  `⟸`: `k = 3c` makes `g^{c}` a cube root
    (`(g^c)^3 = g^{3c} = g^k`).  ∅-axiom. -/
theorem cube_pow_iff_three_dvd_exp (p m g : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m) (hg1 : 1 ≤ g) (hgle : g ≤ p - 1)
    (hord : ordModP g p = p - 1) (k : Nat) :
    (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 3 % p = g ^ k % p) ↔ 3 ∣ k := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  constructor
  · rintro ⟨x, hx1, hxlt, hx3⟩
    have hgkm1 : (g ^ k) ^ m % p = 1 := by
      rw [pow_mod_base (g ^ k) p m, ← hx3, ← pow_mod_base (x ^ 3) p m, ← pow_mul_loc x 3 m, h3m]
      exact fermat x p hp hpr hx1 hxlt
    have hkm : g ^ (k * m) % p = 1 := by rw [pow_mul_loc g k m]; exact hgkm1
    have hord_dvd : ordModP g p ∣ k * m :=
      (pow_one_iff_ord_dvd g p hp hpr hg1 hglt (k * m)).mp hkm
    rw [hord, ← h3m] at hord_dvd
    exact (three_mul_dvd_iff m k hm1).mp hord_dvd
  · intro h
    obtain ⟨c, hc⟩ := h
    have hgc_unit : ¬ p ∣ g ^ c := not_dvd_pow g p c hp hpr (not_dvd_g g p hg1 hglt)
    refine ⟨g ^ c % p, ?_, Nat.mod_lt _ hppos, ?_⟩
    · rcases Nat.eq_zero_or_pos (g ^ c % p) with h0 | hpos
      · exact absurd (dvd_of_mod_eq_zero h0) hgc_unit
      · exact hpos
    · rw [← pow_mod_base (g ^ c) p 3, ← pow_mul_loc g c 3, hc, Nat.mul_comm c 3]

/-- ★★★★★ **The cubic character of a unit is its discrete-log mod-3 class** (fully-internal form).
    For a prime `p` (`3m = p − 1`) and any unit `a` (`1 ≤ a < p`), there is a primitive root `g` and
    a discrete log `k` with `a ≡ g^k (mod p)` such that **`a` is a cubic residue ⟺ `3 ∣ k`**.  The
    cubes are exactly the units at orbit positions `≡ 0 (mod 3)` in the cyclic group `⟨g⟩`.  Native
    `exists_primitive_root` + `dlog_exists` feed `cube_pow_iff_three_dvd_exp`.  ∅-axiom. -/
theorem cube_iff_three_dvd_dlog (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    ∃ g k, (1 ≤ g ∧ g ≤ p - 1 ∧ ordModP g p = p - 1) ∧ a = g ^ k % p ∧
      ((∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 3 % p = a) ↔ 3 ∣ k) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  obtain ⟨g, hg1, hgle, hord⟩ := exists_primitive_root p hp hpr
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  obtain ⟨k, hak⟩ := dlog_exists p g a hp hpr hg1 hglt hord ha1 halt
  refine ⟨g, k, ⟨hg1, hgle, hord⟩, hak.symm, ?_⟩
  rw [← hak]
  exact cube_pow_iff_three_dvd_exp p m g hp hpr h3m hm1 hg1 hgle hord k

end E213.Lib.Math.NumberTheory.ModArith.CubicResidue
