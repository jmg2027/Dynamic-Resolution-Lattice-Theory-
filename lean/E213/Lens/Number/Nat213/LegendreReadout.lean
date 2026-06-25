import E213.Lens.Number.Nat213.ModArithReadout
import E213.Meta.Nat.ModPow213
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.Pow213
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative
import E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity
import E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement
import E213.Lib.Math.NumberTheory.ModArith.SecondSupplement

/-!
# Lens.Number.Nat213.LegendreReadout — the quadratic-residue / Legendre corpus over `Nat213` (∅-axiom)

The **descent leg**, leg-2 — the **quadratic-residue** theory transported onto the Raw-generated
carrier, capped by the **law of quadratic reciprocity**.

The native corpus expresses "`a` is a quadratic residue mod `p`" as an inline bounded existential
`∃ z, 1 ≤ z ∧ z < p ∧ z² % p = a % p`.  The carrier-native object is cleaner — a congruence:

  `QR p a := ∃ z : Nat213, z² ≡ a (mod p)`

with **no bounds** (the carrier ranges freely; the bound is a Lens artifact of choosing one residue
representative).  The one-time weld `QR_iff_native` reconciles the two readings — it lifts the carrier
square out (`modeq_toNat_mod_iff` + `toNat_powNat`) and reduces a free witness mod `p` back to the
bounded range, using the **unit** hypothesis `¬ p ∣ a` (without it `z` could reduce to `0`, off the
`1 ≤ z` range — the no-zero gap again).  With that bridge the corpus transports, each headline built
by **composing iffs** (`Iff.trans`/`.mp`/`.mpr`, never `rw` on a `Prop` — that would pull `propext`):

* `legendre_mul` — the Legendre symbol is multiplicative: `QR p (a·b) ⟺ (QR p a ⟺ QR p b)`;
* `quadratic_reciprocity` — for distinct odd primes, `QR p q ⟺ QR q p` iff `m·n` is even;
* `first_supplement` — `−1` (the residue `p−1`) is a QR iff `p ≡ 1 (mod 4)`;
* `second_supplement` — `2` is a QR iff `p ≡ ±1 (mod 8)`.

Native source: `Lib/.../ModArith/{LegendreMultiplicative, QuadraticReciprocity, EulerFirstSupplement,
SecondSupplement}`.  Transported, not re-derived.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.LegendreReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (powNat mul two toNat toNat_ge_one toNat_mul)
open E213.Lens.Number.Nat213.ToNatReadout (toNat_surj toNat_powNat)
open E213.Lens.Number.Nat213.Congruence (ModEq)
open E213.Lens.Number.Nat213.ModArithReadout (modeq_of_toNat_mod modeq_imp_toNat_mod)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Tactic.NatHelper (zero_mod le_sub_of_add_le)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (legendre_mul)
open E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity (quadratic_reciprocity)
open E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement (neg_one_qr_iff)
open E213.Lib.Math.NumberTheory.ModArith.SecondSupplement (second_supplement)

/-- **Quadratic residue over `Nat213`** — `a` is a QR mod `p` iff some carrier square is congruent to
    `a`: `∃ z : Nat213, z² ≡ a (mod p)`.  Subtraction-free, bound-free — the carrier-native reading
    of the Legendre numerator. -/
def QR (p a : Nat213) : Prop := ∃ z : Nat213, ModEq p (powNat z 2) a

/-- ★★★ **The QR weld** — for a unit `a` (`¬ p ∣ a.toNat`), the carrier `QR p a` matches the native
    bounded existential: `QR p a ⟺ ∃ z, 1 ≤ z ∧ z < p.toNat ∧ z² % p.toNat = a.toNat % p.toNat`.
    ⟹ reduces a free carrier witness mod `p` (still `≥ 1` because `a` is a unit, else the square
    would be `≡ 0`); ⟸ lifts the bounded native witness through `toNat_surj`.  ∅-axiom. -/
theorem QR_iff_native {p a : Nat213} (hp : 1 < p.toNat) (hunit : ¬ p.toNat ∣ a.toNat) :
    QR p a ↔ ∃ z : Nat, 1 ≤ z ∧ z < p.toNat ∧ z ^ 2 % p.toNat = a.toNat % p.toNat := by
  have hppos : 0 < p.toNat := Nat.lt_trans Nat.zero_lt_one hp
  constructor
  · rintro ⟨z, hz⟩
    have hzm : z.toNat ^ 2 % p.toNat = a.toNat % p.toNat := by
      have h := modeq_imp_toNat_mod hz; rwa [toNat_powNat] at h
    refine ⟨z.toNat % p.toNat, ?_, Nat.mod_lt _ hppos, ?_⟩
    · rcases Nat.eq_zero_or_pos (z.toNat % p.toNat) with h0 | hpos
      · exfalso
        have hz0sq : z.toNat ^ 2 % p.toNat = 0 := by
          rw [pow_mod_base z.toNat p.toNat 2, h0]; exact zero_mod p.toNat
        rw [hz0sq] at hzm
        exact hunit (dvd_of_mod_eq_zero hzm.symm)
      · exact hpos
    · rw [← pow_mod_base]; exact hzm
  · rintro ⟨z, hz1, _, hzeq⟩
    obtain ⟨z', hz'⟩ := toNat_surj z hz1
    refine ⟨z', ?_⟩
    apply modeq_of_toNat_mod
    rw [toNat_powNat, hz']; exact hzeq

/-- ★★★★★ **The Legendre symbol is multiplicative** — `QR p (a·b) ⟺ (QR p a ⟺ QR p b)`, for a prime
    `p` (`2m = p−1`) and units `a, b < p`.  The defining homomorphism `(·/p) : (ℤ/p)* → {±1}`.
    Native `legendre_mul` composed through `QR_iff_native` (per side; the product side via
    `toNat_mul`, the factor sides via `a.toNat % p = a.toNat` as `a < p`).  ∅-axiom. -/
theorem legendre_mul_t {p a b : Nat213} (m : Nat) (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (h2m : 2 * m = p.toNat - 1) (hm1 : 1 ≤ m)
    (halt : a.toNat < p.toNat) (hblt : b.toNat < p.toNat) :
    QR p (mul a b) ↔ (QR p a ↔ QR p b) := by
  have hua : ¬ p.toNat ∣ a.toNat :=
    fun h => absurd (le_of_dvd_pos p.toNat a.toNat (toNat_ge_one a) h) (Nat.not_le.mpr halt)
  have hub : ¬ p.toNat ∣ b.toNat :=
    fun h => absurd (le_of_dvd_pos p.toNat b.toNat (toNat_ge_one b) h) (Nat.not_le.mpr hblt)
  have huab : ¬ p.toNat ∣ (a.toNat * b.toNat) :=
    fun h => (nat_prime_dvd_mul p.toNat hp hpr a.toNat b.toNat h).elim hua hub
  have qa : QR p a ↔ ∃ x : Nat, 1 ≤ x ∧ x < p.toNat ∧ x ^ 2 % p.toNat = a.toNat := by
    have h := QR_iff_native hp hua; rw [Nat.mod_eq_of_lt halt] at h; exact h
  have qb : QR p b ↔ ∃ y : Nat, 1 ≤ y ∧ y < p.toNat ∧ y ^ 2 % p.toNat = b.toNat := by
    have h := QR_iff_native hp hub; rw [Nat.mod_eq_of_lt hblt] at h; exact h
  have qab : QR p (mul a b) ↔
      ∃ z : Nat, 1 ≤ z ∧ z < p.toNat ∧ z ^ 2 % p.toNat = (a.toNat * b.toNat) % p.toNat := by
    have h := QR_iff_native hp (by rw [toNat_mul]; exact huab); rw [toNat_mul] at h; exact h
  have key := legendre_mul p.toNat m a.toNat b.toNat hp hpr h2m hm1
    (toNat_ge_one a) halt (toNat_ge_one b) hblt
  constructor
  · intro h; exact qa.trans (Iff.trans (key.mp (qab.mp h)) qb.symm)
  · intro h; exact qab.mpr (key.mpr (qa.symm.trans (h.trans qb)))

/-- ★★★★★ **The law of quadratic reciprocity over `Nat213`** — for distinct odd primes `p`, `q`
    (`2m = p−1`, `2n = q−1`): `q` is a QR mod `p` **iff** `p` is a QR mod `q`, exactly when `m·n` is
    even (i.e. unless `p ≡ q ≡ 3 mod 4`): `(QR p q ⟺ QR q p) ⟺ (m·n) % 2 = 0`.  Native
    `quadratic_reciprocity` welded through `QR_iff_native` both sides (the `%`-form matches directly;
    distinctness gives the unit hypotheses `p ∤ q`, `q ∤ p`).  ∅-axiom. -/
theorem quadratic_reciprocity_t {p q : Nat213} (m n : Nat)
    (hp : 1 < p.toNat) (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (hp2 : 2 < p.toNat)
    (hpm : 2 * m = p.toNat - 1) (hm1 : 1 ≤ m) (hpodd : p.toNat % 2 = 1)
    (hq : 1 < q.toNat) (hqr : ∀ d, d ∣ q.toNat → d = 1 ∨ d = q.toNat) (hq2 : 2 < q.toNat)
    (hqn : 2 * n = q.toNat - 1) (hn1 : 1 ≤ n) (hqodd : q.toNat % 2 = 1)
    (hpqne : p.toNat ≠ q.toNat) :
    (QR p q ↔ QR q p) ↔ (m * n) % 2 = 0 := by
  have hpq : ¬ p.toNat ∣ q.toNat :=
    fun h => (hqr p.toNat h).elim (fun e => absurd e (Nat.ne_of_gt hp)) hpqne
  have hqp : ¬ q.toNat ∣ p.toNat :=
    fun h => (hpr q.toNat h).elim (fun e => absurd e (Nat.ne_of_gt hq)) (fun e => hpqne e.symm)
  have bp := QR_iff_native hp hpq
  have bq := QR_iff_native hq hqp
  have key := quadratic_reciprocity p.toNat q.toNat m n hp hpr hp2 hpm hm1 hpodd
    hq hqr hq2 hqn hn1 hqodd hpqne
  constructor
  · intro h; exact key.mp (bp.symm.trans (h.trans bq))
  · intro h; exact bp.trans ((key.mpr h).trans bq.symm)

/-- ★★★★★ **First supplement** — `−1` (the residue `c` with `c.toNat = p − 1`) is a QR mod a prime
    `p` **iff** `p ≡ 1 (mod 4)`: `QR p c ⟺ p.toNat % 4 = 1`.  Native `neg_one_qr_iff` welded through
    `QR_iff_native` (`p − 1` is a unit: `1 ≤ p−1 < p`).  ∅-axiom. -/
theorem first_supplement {p c : Nat213} (m : Nat) (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (h2m : 2 * m = p.toNat - 1) (hm1 : 1 ≤ m)
    (hc : c.toNat = p.toNat - 1) : QR p c ↔ p.toNat % 4 = 1 := by
  have hppos : 0 < p.toNat := Nat.lt_trans Nat.zero_lt_one hp
  have hp1le : 1 ≤ p.toNat - 1 := le_sub_of_add_le hp
  have hlt : p.toNat - 1 < p.toNat := Nat.sub_lt hppos Nat.zero_lt_one
  have hunit : ¬ p.toNat ∣ c.toNat := by
    rw [hc]; exact fun h => absurd (le_of_dvd_pos p.toNat _ hp1le h) (Nat.not_le.mpr hlt)
  have b := QR_iff_native hp hunit
  rw [hc, Nat.mod_eq_of_lt hlt] at b
  exact b.trans (neg_one_qr_iff p.toNat m hp hpr h2m hm1)

/-- ★★★★★ **Second supplement** — `2` is a QR mod a prime `p` (`p > 2`) **iff** `p ≡ ±1 (mod 8)`:
    `QR p two ⟺ p.toNat % 8 = 1 ∨ p.toNat % 8 = 7`.  Native `second_supplement` welded through
    `QR_iff_native` (`2` is a unit since `p > 2`).  ∅-axiom. -/
theorem second_supplement_t {p : Nat213} (m : Nat) (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (h2m : 2 * m = p.toNat - 1) (hm1 : 1 ≤ m)
    (hp2 : 2 < p.toNat) : QR p two ↔ p.toNat % 8 = 1 ∨ p.toNat % 8 = 7 := by
  have hunit : ¬ p.toNat ∣ two.toNat :=
    fun h => absurd (le_of_dvd_pos p.toNat two.toNat (by decide) h) (Nat.not_le.mpr hp2)
  have b := QR_iff_native hp hunit
  rw [show two.toNat = 2 from rfl, Nat.mod_eq_of_lt hp2] at b
  exact b.trans (second_supplement p.toNat m hp hpr h2m hm1 hp2)

end E213.Lens.Number.Nat213.LegendreReadout
