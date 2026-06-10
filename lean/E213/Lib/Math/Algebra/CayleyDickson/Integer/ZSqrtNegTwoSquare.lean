import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSplit
import E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative
import E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement
import E213.Lib.Math.NumberTheory.ModArith.SecondSupplement
import E213.Lib.Math.NumberTheory.ModArith.EulerConverse
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Meta.Int213.PolyIntMTactic

/-!
# ZSqrtNegTwoSquare — the disc-`−8` representation iff `p = a² + 2b² ⟺ p ≡ 1,3 (mod 8)`

The `ℤ[√−2]` capstone, the disc-`−8` twin of `GaussianTwoSquare` (disc-`−4`).  The forward
half — *which* odd primes represent — is the one input the multiplicative norm-Euclidean engine
(`ZSqrtNegSplit.split_form_two`: `p ∣ x²+2 ⟹ p = a²+2b²`) lacked: the quadratic character of
`−2`.  That character is assembled from two already-closed supplements, multiplied by the
Legendre homomorphism:

  * `(−2/p) = (−1/p)·(2/p)`  (`LegendreMultiplicative.legendre_mul` at `a = p−1`, `b = 2`,
    using `((p−1)·2) % p = p − 2`),
  * `(−1/p) = 1 ⟺ p ≡ 1 (mod 4)`  (`EulerFirstSupplement.neg_one_qr_iff`),
  * `(2/p)  = 1 ⟺ p ≡ ±1 (mod 8)`  (`SecondSupplement.second_supplement`).

The two characters agree (so `−2` is a QR) exactly on `p ≡ 1, 3 (mod 8)`; then `−2` a QR gives
`p ∣ z²+2`, and the split produces `p = a²+2b²`.

  * ★★★★★ `rep_of_mod8`  — `p` prime, `p ≡ 1,3 (mod 8)` ⟹ `∃ a b : Int, ↑p = a²+2b²`.
  * ★★★★  `mod8_of_rep`  — necessity: an odd prime `a²+2b²` is `≡ 1` or `3 (mod 8)`.
  * ★★★★★ `disc_neg_eight_iff` — the full iff.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegTwoSquare

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSplit (split_form_two)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (legendre_mul)
open E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement (neg_one_qr_iff)
open E213.Lib.Math.NumberTheory.ModArith.SecondSupplement (second_supplement)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (sq_nat natCast_sub mod_eq_of_dvd_sub)
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (mod_one_of_dvd_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int)
open E213.Lib.Math.NumberTheory.PolyRoot (nat_dvd_to_int int_dvd_to_nat dvd_add')
open E213.Meta.Nat.AddMod213 (div_add_mod dvd_of_mod_eq_zero)
open E213.Meta.Nat.NatRing213 (nat_add_sub_self_right nat_sub_add_cancel)
open E213.Tactic.NatHelper (add_mul_mod_self_pure cases_lt_two cases_lt_five le_sub_of_add_le)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §1 — squares and `2·square` modulo 8 -/

/-- `2·|r| ≤ 8` ⟹ `r ∈ {−4,…,4}`. -/
theorem int_small8 (r : Int) (h : 2 * r.natAbs ≤ 8) :
    r = -4 ∨ r = -3 ∨ r = -2 ∨ r = -1 ∨ r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by
  have hle : r.natAbs ≤ 4 := by
    rcases Nat.lt_or_ge r.natAbs 5 with hlt | hge
    · exact Nat.le_of_lt_succ hlt
    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 2 hge) h) (by decide)
  rcases Int.natAbs_eq r with he | he
  · rcases cases_lt_five (Nat.lt_succ_of_le hle) with h0 | h1 | h2 | h3 | h4
    · right;right;right;right;left; rw [he, h0]; decide
    · right;right;right;right;right;left; rw [he, h1]; decide
    · right;right;right;right;right;right;left; rw [he, h2]; decide
    · right;right;right;right;right;right;right;left; rw [he, h3]; decide
    · right;right;right;right;right;right;right;right; rw [he, h4]; decide
  · rcases cases_lt_five (Nat.lt_succ_of_le hle) with h0 | h1 | h2 | h3 | h4
    · right;right;right;right;left; rw [he, h0]; decide
    · right;right;right;left; rw [he, h1]; decide
    · right;right;left; rw [he, h2]; decide
    · right;left; rw [he, h3]; decide
    · left; rw [he, h4]; decide

/-- A perfect square is `≡ 0, 1`, or `4 (mod 8)`. -/
theorem sq8 (c : Int) : (8 : Int) ∣ (c * c) ∨ (8 : Int) ∣ (c * c - 1) ∨ (8 : Int) ∣ (c * c - 4) := by
  obtain ⟨q, r, hd, hr⟩ := centered_div_int c 8 (by decide)
  rw [show (8 : Int).natAbs = 8 from rfl] at hr
  have hpack : (8 : Int) ∣ (c * c - r * r) := ⟨8 * q * q + 2 * q * r, by rw [hd]; ring_intZ⟩
  rcases int_small8 r hr with h|h|h|h|h|h|h|h|h
  · -- r = -4: r*r = 16; c*c = (c*c - 16) + 16, 8 ∣ both
    left
    have e : c * c - r * r = c * c - 16 := by rw [h]; ring_intZ
    have hcc : c * c = (c * c - 16) + 16 := by ring_intZ
    rw [hcc]; exact dvd_add' (e ▸ hpack) ⟨2, by ring_intZ⟩
  · -- r = -3: r*r = 9; c*c - 9 = (c*c - 1) - 8
    right; left
    have e : c * c - r * r = (c * c - 1) - 8 := by rw [h]; ring_intZ
    have : c * c - 1 = (c * c - r * r) + 8 := by rw [e]; ring_intZ
    rw [this]; exact dvd_add' hpack ⟨1, by ring_intZ⟩
  · right; right
    have e : c * c - r * r = c * c - 4 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack
  · right; left
    have e : c * c - r * r = c * c - 1 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack
  · left
    have e : c * c - r * r = c * c := by rw [h, show (0 : Int) * 0 = 0 from rfl,
      E213.Meta.Int213.Order.sub_zero]
    rw [e] at hpack; exact hpack
  · right; left
    have e : c * c - r * r = c * c - 1 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack
  · right; right
    have e : c * c - r * r = c * c - 4 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack
  · right; left
    have e : c * c - r * r = (c * c - 1) - 8 := by rw [h]; ring_intZ
    have : c * c - 1 = (c * c - r * r) + 8 := by rw [e]; ring_intZ
    rw [this]; exact dvd_add' hpack ⟨1, by ring_intZ⟩
  · left
    have e : c * c - r * r = c * c - 16 := by rw [h]; ring_intZ
    have hcc : c * c = (c * c - 16) + 16 := by ring_intZ
    rw [hcc]; exact dvd_add' (e ▸ hpack) ⟨2, by ring_intZ⟩

/-- `2·b²` is `≡ 0` or `2 (mod 8)`. -/
theorem two_sq8 (b : Int) : (8 : Int) ∣ (2 * (b * b)) ∨ (8 : Int) ∣ (2 * (b * b) - 2) := by
  rcases sq8 b with h | h | h
  · left
    obtain ⟨k, hk⟩ := h
    exact ⟨2 * k, by rw [show 2 * (b * b) = 2 * (b * b) from rfl, hk]; ring_intZ⟩
  · right
    obtain ⟨k, hk⟩ := h
    exact ⟨2 * k, by
      have : 2 * (b * b) - 2 = 2 * (b * b - 1) := by ring_intZ
      rw [this, hk]; ring_intZ⟩
  · left
    obtain ⟨k, hk⟩ := h
    refine ⟨2 * k + 1, ?_⟩
    have hb : b * b = (b * b - 4) + 4 := by ring_intZ
    rw [hb, hk]; ring_intZ

/-! ## §2 — necessity: an odd `a²+2b²` is `≡ 1` or `3 (mod 8)` -/

/-- `a² + 2b²` lands in `{0,1,2,3,4,6} (mod 8)` (the achievable residues), in the disjunction
    order `v, v−1, v−2, v−3, v−4, v−6`. -/
theorem form8_residue (a b : Int) :
    (8 : Int) ∣ (a*a + 2*(b*b)) ∨ (8 : Int) ∣ (a*a + 2*(b*b) - 1) ∨ (8 : Int) ∣ (a*a + 2*(b*b) - 2)
      ∨ (8 : Int) ∣ (a*a + 2*(b*b) - 3) ∨ (8 : Int) ∣ (a*a + 2*(b*b) - 4)
      ∨ (8 : Int) ∣ (a*a + 2*(b*b) - 6) := by
  rcases sq8 a with ha | ha | ha <;> rcases two_sq8 b with hb | hb
  · left; exact dvd_add' ha hb
  · right; right; left
    have e : a*a + 2*(b*b) - 2 = (a*a) + (2*(b*b) - 2) := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · right; left
    have e : a*a + 2*(b*b) - 1 = (a*a - 1) + 2*(b*b) := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · right; right; right; left
    have e : a*a + 2*(b*b) - 3 = (a*a - 1) + (2*(b*b) - 2) := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · right; right; right; right; left
    have e : a*a + 2*(b*b) - 4 = (a*a - 4) + 2*(b*b) := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · right; right; right; right; right
    have e : a*a + 2*(b*b) - 6 = (a*a - 4) + (2*(b*b) - 2) := by ring_intZ
    rw [e]; exact dvd_add' ha hb

/-- ★★★★ **Necessity.**  An odd prime `p` of the form `a² + 2b²` satisfies `p ≡ 1` or `3 (mod 8)`.
    The even residues `{0,2,4,6}` force `2 ∣ p`; only `1, 3` survive oddness. -/
theorem mod8_of_rep (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hp2 : 2 < p) (a b : Int) (hrep : (p : Int) = a * a + 2 * (b * b)) :
    p % 8 = 1 ∨ p % 8 = 3 := by
  have hodd : ¬ 2 ∣ p := by
    intro hd; rcases hpr 2 hd with h | h
    · exact absurd h (by decide)
    · rw [← h] at hp2; exact absurd hp2 (by decide)
  -- helper: 2 ∣ (p:Int) contradicts oddness
  have even_absurd : (2 : Int) ∣ (p : Int) → False := by
    intro h2p
    exact hodd (by rw [← Int.natAbs_ofNat p]; exact int_dvd_to_nat 2 (p : Int) h2p)
  rcases form8_residue a b with h0 | h1 | h2 | h3 | h4 | h6
  · exfalso; rw [← hrep] at h0; obtain ⟨c, hc⟩ := h0
    exact even_absurd ⟨4 * c, by rw [hc]; ring_intZ⟩
  · -- p − 1 ≡ 0 (mod 8) ⟹ p % 8 = 1
    left
    rw [← hrep, ← natCast_sub_one p (Nat.le_of_lt hp)] at h1
    have hnat : 8 ∣ (p - 1) := by
      rw [← Int.natAbs_ofNat (p - 1)]; exact int_dvd_to_nat 8 ((p - 1 : Nat) : Int) h1
    exact mod_one_of_dvd_sub_one 8 p (by decide) (Nat.le_of_lt hp) hnat
  · exfalso; rw [← hrep] at h2; obtain ⟨c, hc⟩ := h2
    have : (p : Int) = 8 * c + 2 := by rw [← hc]; ring_intZ
    exact even_absurd ⟨4 * c + 1, by rw [this]; ring_intZ⟩
  · -- p − 3 ≡ 0 (mod 8) ⟹ p % 8 = 3
    right
    have hcast : ((p - 3 : Nat) : Int) = (p : Int) - 3 := natCast_sub p 3 hp2
    rw [← hrep, ← hcast] at h3
    have hnat : 8 ∣ (p - 3) := by
      rw [← Int.natAbs_ofNat (p - 3)]; exact int_dvd_to_nat 8 ((p - 3 : Nat) : Int) h3
    have := mod_eq_of_dvd_sub 8 p 3 hp2 hnat
    rwa [show (3 : Nat) % 8 = 3 from rfl] at this
  · exfalso; rw [← hrep] at h4; obtain ⟨c, hc⟩ := h4
    have : (p : Int) = 8 * c + 4 := by rw [← hc]; ring_intZ
    exact even_absurd ⟨4 * c + 2, by rw [this]; ring_intZ⟩
  · exfalso; rw [← hrep] at h6; obtain ⟨c, hc⟩ := h6
    have : (p : Int) = 8 * c + 6 := by rw [← hc]; ring_intZ
    exact even_absurd ⟨4 * c + 3, by rw [this]; ring_intZ⟩

/-! ## §3 — sufficiency: `p ≡ 1,3 (mod 8)` ⟹ `−2` a QR ⟹ representation -/

/-- `p` odd (`p % 2 = 1`) for a prime `p > 2`. -/
private theorem prime_odd (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hp2 : 2 < p) :
    p % 2 = 1 := by
  have hodd : ¬ 2 ∣ p := by
    intro hd; rcases hpr 2 hd with h | h
    · exact absurd h (by decide)
    · rw [← h] at hp2; exact absurd hp2 (by decide)
  rcases cases_lt_two (Nat.mod_lt p (by decide)) with h0 | h1
  · exact absurd (dvd_of_mod_eq_zero h0) hodd
  · exact h1

/-- The half-system witness: `2·m = p − 1` with `1 ≤ m`, for an odd prime `p > 2`. -/
private theorem half_system (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hp2 : 2 < p) :
    ∃ m, 2 * m = p - 1 ∧ 1 ≤ m := by
  have hodd := prime_odd p hpr hp2
  obtain ⟨Q, hQ⟩ : ∃ Q, p / 2 = Q := ⟨_, rfl⟩
  have hdm : 2 * Q + p % 2 = p := by rw [← hQ]; exact div_add_mod p 2
  rw [hodd] at hdm        -- 2*Q + 1 = p
  refine ⟨Q, ?_, ?_⟩
  · rw [← hdm, nat_add_sub_self_right]
  · rcases Nat.eq_zero_or_pos Q with h0 | hpos
    · exfalso
      rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
      rw [← hdm] at hp2; exact absurd hp2 (by decide)
    · exact hpos

/-- `((p−1)·2) % p = p − 2` for `p > 2`. -/
private theorem neg_two_residue (p : Nat) (hp2 : 2 < p) : ((p - 1) * 2) % p = p - 2 := by
  obtain ⟨d, hd⟩ : ∃ d, p = d + 2 := ⟨p - 2, (nat_sub_add_cancel (Nat.le_of_lt hp2)).symm⟩
  subst hd
  rw [show d + 2 - 1 = d + 1 from by rw [show d + 2 = (d + 1) + 1 from rfl, nat_add_sub_self_right],
      show d + 2 - 2 = d from nat_add_sub_self_right d 2]
  have e : (d + 1) * 2 = d + 1 * (d + 2) := by ring_nat
  rw [e, add_mul_mod_self_pure]
  exact Nat.mod_eq_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self d))

/-- `p % 8 = r ⟹ p % 4 = r % 4` (the mod-8 → mod-4 reduction, `r < 8`). -/
private theorem pmod4_of_pmod8 (p r : Nat) (h : p % 8 = r) : p % 4 = r % 4 := by
  obtain ⟨Q, hQ⟩ : ∃ Q, p / 8 = Q := ⟨_, rfl⟩
  have hdm : 8 * Q + p % 8 = p := by rw [← hQ]; exact div_add_mod p 8
  rw [h] at hdm           -- 8*Q + r = p
  have e : p = r + (Q * 2) * 4 := by rw [← hdm]; ring_nat
  rw [e, add_mul_mod_self_pure]

/-! ## §3b — the sufficiency theorem -/

/-- ★★★★★ **Sufficiency (the disc-`−8` representation).**  A prime `p ≡ 1` or `3 (mod 8)` is of
    the form `a² + 2b²`: `∃ a b : Int, ↑p = a² + 2b²`.  The character `(−2/p) = (−1/p)·(2/p)`
    is `+1` exactly on these residues, giving `p ∣ z²+2`, fed to the `ℤ[√−2]` descent. -/
theorem rep_of_mod8 (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hp2 : 2 < p) (hmod : p % 8 = 1 ∨ p % 8 = 3) :
    ∃ a b : Int, (p : Int) = a * a + 2 * (b * b) := by
  obtain ⟨m, h2m, hm1⟩ := half_system p hpr hp2
  -- units p−1 and 2
  have hp1lt : p - 1 < p := Nat.sub_lt (Nat.lt_trans (by decide) hp2) (by decide)
  have hp1pos : 1 ≤ p - 1 := le_sub_of_add_le (show 1 + 1 ≤ p from Nat.le_of_lt hp2)
  -- the −2 character: (∃z, z²%p = p−2) ⟺ ((−1 QR) ⟺ (2 QR))
  have hleg := legendre_mul p m (p - 1) 2 hp hpr h2m hm1 hp1pos hp1lt (by decide) hp2
  rw [neg_two_residue p hp2] at hleg
  -- the two supplements
  have hneg1 := neg_one_qr_iff p m hp hpr h2m hm1
  have h2nd := second_supplement p m hp hpr h2m hm1 hp2
  -- show −2 is a QR, by cases on p % 8
  have hqr : ∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = p - 2 := by
    apply hleg.mpr
    rcases hmod with h1 | h3
    · -- p % 8 = 1: both characters hold
      have hp4 : p % 4 = 1 := pmod4_of_pmod8 p 1 h1
      have hA : ∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = p - 1 := hneg1.mpr hp4
      have hB : ∃ y : Nat, 1 ≤ y ∧ y < p ∧ y ^ 2 % p = 2 := h2nd.mpr (Or.inl h1)
      exact Iff.intro (fun _ => hB) (fun _ => hA)
    · -- p % 8 = 3: both characters fail
      have hp4 : p % 4 = 3 := pmod4_of_pmod8 p 3 h3
      have hnA : ¬ (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = p - 1) := by
        intro hx; rw [hneg1.mp hx] at hp4; exact absurd hp4 (by decide)
      have hnB : ¬ (∃ y : Nat, 1 ≤ y ∧ y < p ∧ y ^ 2 % p = 2) := by
        intro hy; rcases h2nd.mp hy with h | h <;> rw [h] at h3 <;> exact absurd h3 (by decide)
      exact Iff.intro (fun hx => absurd hx hnA) (fun hy => absurd hy hnB)
  -- −2 a QR ⟹ p ∣ z²+2 ⟹ split
  obtain ⟨z, _, _, hz⟩ := hqr
  have hpz : p ∣ (z * z + 2) := by
    have hdm : p * (z * z / p) + (z * z) % p = z * z := div_add_mod (z * z) p
    rw [sq_nat z] at hz
    obtain ⟨Q, hQ⟩ : ∃ Q, z * z / p = Q := ⟨_, rfl⟩
    rw [hz, hQ] at hdm
    -- hdm : p * Q + (p − 2) = z * z
    refine ⟨Q + 1, ?_⟩
    have hpge2 : 2 ≤ p := Nat.le_of_lt hp2
    -- z*z + 2 = p*Q + (p−2) + 2 = p*Q + p = p*(Q + 1)
    rw [← hdm, Nat.add_assoc, nat_sub_add_cancel hpge2]
    ring_nat
  have hpzInt : (p : Int) ∣ ((z : Int) * (z : Int) + 2) := by
    have hcast : ((z * z + 2 : Nat) : Int) = (z : Int) * (z : Int) + 2 := by
      rw [Int.ofNat_add, Int.ofNat_mul]; rfl
    rw [← hcast]
    exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact hpz)
  have hp1ne : ¬ ((p : Int) ∣ (1 : Int)) := by
    intro hd
    have hle := le_of_dvd_pos p (Int.natAbs (1 : Int)) (by decide) (int_dvd_to_nat p 1 hd)
    rw [show Int.natAbs (1 : Int) = 1 from rfl] at hle
    exact absurd hle (Nat.not_le.mpr hp)
  exact split_form_two p (Nat.le_of_lt hp2) hpr hp1ne (z : Int) hpzInt

/-! ## §4 — the full iff -/

/-- ★★★★★ **The disc-`−8` representation iff.**  For a prime `p > 2`:
    `(∃ a b : Int, ↑p = a² + 2b²) ⟺ p ≡ 1` or `3 (mod 8)`. -/
theorem disc_neg_eight_iff (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hp2 : 2 < p) :
    (∃ a b : Int, (p : Int) = a * a + 2 * (b * b)) ↔ (p % 8 = 1 ∨ p % 8 = 3) := by
  constructor
  · rintro ⟨a, b, hrep⟩; exact mod8_of_rep p hp hpr hp2 a b hrep
  · intro hmod; exact rep_of_mod8 p hp hpr hp2 hmod

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegTwoSquare
