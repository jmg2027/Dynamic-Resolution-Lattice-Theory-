import E213.Lib.Math.NumberTheory.ModArith.OrderPow
import E213.Lib.Math.NumberTheory.ModArith.CoprimeOrder
import E213.Lib.Math.NumberTheory.ModArith.MaxOrder
import E213.Lib.Math.NumberTheory.ModArith.QPart
import E213.Lib.Math.NumberTheory.ModArith.ValuationAlg
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PolyNatMTactic

/-!
# EveryOrdDvdMax — "every order divides `maxOrd`" (marathon brick 4b-iv, the exponent argument)

  * ★★★★ `every_ord_dvd_maxOrd` — for a unit `a`, `ordModP a p ∣ maxOrd p`.

If not, `exists_prime_vp_gt` gives a prime `q` with `vp_q(ord a) > vp_q(maxOrd)`.  Build
`x = (a^(ord a / A))%p` of order `A = qpart q (ord a)` and `y = (g^(qpart q d))%p` of order
`B = d/qpart q d` (`g` the `maxOrd`-achiever); `gcd(A,B)=1`, so `ord((x·y)%p) = A·B ≥ q·d > d`
(`ord_mul_coprime`) — contradicting `maxOrd_ge`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.EveryOrdDvdMax

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP ord_pos)
open E213.Lib.Math.NumberTheory.ModArith.OrderPow (ord_pow ord_mod_eq not_dvd_pow)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeOrder (ord_mul_coprime)
open E213.Lib.Math.NumberTheory.ModArith.MaxOrder (maxOrd maxOrd_ge maxOrd_achieved one_le_maxOrd)
open E213.Lib.Math.NumberTheory.ModArith.QPart
  (qpart qpart_dvd qpart_pos q_not_dvd_quot gcd_eq_of_dvd gcd_qpow_qfree)
open E213.Lib.Math.NumberTheory.ModArith.ValuationAlg (exists_prime_vp_gt)
open E213.Meta.Nat.Valuation (vp mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberTheory.Lcm213 (mul_div_cancel_of_dvd)
open E213.Meta.Nat.NatDiv213 (mul_div_self_pure)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Tactic.NatHelper (gcd213)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §1 — order-of-a-power helpers -/

/-- For a unit `a` and `k ∣ ord a` (`k ≥ 1`): `ordModP (aᵏ) p = ord a / k`. -/
theorem ord_pow_div (a p k : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) (hk1 : 1 ≤ k) (hkd : k ∣ ordModP a p) :
    ordModP (a ^ k) p = ordModP a p / k := by
  rw [ord_pow a p k hp hpr ha0 halt hk1, gcd_eq_of_dvd hkd]

/-- For a unit `a` and `A ∣ ord a`: `ordModP (a^(ord a / A)) p = A`. -/
theorem ord_pow_eq_of_dvd (a p A : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) (hA : A ∣ ordModP a p) :
    ordModP (a ^ (ordModP a p / A)) p = A := by
  obtain ⟨α, hαdef⟩ : ∃ α, ordModP a p = α := ⟨_, rfl⟩
  have hαpos : 0 < α := hαdef ▸ ord_pos a p hp hpr ha0 halt
  rw [hαdef] at hA
  have hApos : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h0 | hp'
    · exfalso; rw [h0] at hA; obtain ⟨c, hc⟩ := hA; rw [Nat.zero_mul] at hc
      rw [hc] at hαpos; exact absurd hαpos (Nat.lt_irrefl 0)
    · exact hp'
  obtain ⟨m, hm⟩ : ∃ m, α / A = m := ⟨_, rfl⟩
  have hAm : A * m = α := by rw [← hm]; exact mul_div_cancel_of_dvd A α hApos hA
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hp'
    · exfalso; rw [h0, Nat.mul_zero] at hAm; rw [← hAm] at hαpos; exact absurd hαpos (Nat.lt_irrefl 0)
    · exact hp'
  have hmα : m ∣ α := ⟨A, by rw [← hAm]; ring_nat⟩
  have hmα' : m ∣ ordModP a p := by rw [hαdef]; exact hmα
  rw [hαdef, hm, ord_pow_div a p m hp hpr ha0 halt hmpos hmα', hαdef, ← hAm]
  exact mul_div_self_pure A m hmpos

/-! ## §2 — every order divides `maxOrd` -/

/-- ★★★★ **Every unit's order divides `maxOrd p`.**  The exponent argument. -/
theorem every_ord_dvd_maxOrd (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (a : Nat) (ha1 : 1 ≤ a) (ha : a ≤ p - 1) : ordModP a p ∣ maxOrd p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hp1lt : p - 1 < p := Nat.sub_lt hppos Nat.zero_lt_one
  have halt : a < p := Nat.lt_of_le_of_lt ha hp1lt
  have ha0 : 0 < a := ha1
  have hαpos0 : 0 < ordModP a p := ord_pos a p hp hpr ha0 halt
  -- pure proof-by-contradiction via the decidable `maxOrd % ord = 0`
  rcases Nat.eq_zero_or_pos (maxOrd p % ordModP a p) with h0 | hposmod
  · exact dvd_of_mod_eq_zero h0
  exfalso
  have hnd : ¬ ordModP a p ∣ maxOrd p := fun hdvd =>
    Nat.lt_irrefl 0 ((mod_zero_of_dvd hαpos0 hdvd) ▸ hposmod)
  have hna : ¬ p ∣ a := fun h => absurd (le_of_dvd_pos p a ha0 h) (Nat.not_le.mpr halt)
  obtain ⟨g, hg1, hgp, hgmax⟩ := maxOrd_achieved p hp
  have hglt : g < p := Nat.lt_of_le_of_lt hgp hp1lt
  have hg0 : 0 < g := hg1
  have hng : ¬ p ∣ g := fun h => absurd (le_of_dvd_pos p g hg0 h) (Nat.not_le.mpr hglt)
  have hαpos : 0 < ordModP a p := ord_pos a p hp hpr ha0 halt
  have hdpos : 0 < maxOrd p := one_le_maxOrd p hp hpr
  obtain ⟨q, hq1, hqpr, hvgt⟩ := exists_prime_vp_gt (ordModP a p) (maxOrd p) hαpos hdpos hnd
  have hq2 : 2 ≤ q := hq1
  -- A = qpart q (ord a),  Qd = qpart q (maxOrd),  B = maxOrd / Qd
  obtain ⟨A, hAdef⟩ : ∃ A, qpart q (ordModP a p) = A := ⟨_, rfl⟩
  obtain ⟨Qd, hQddef⟩ : ∃ Qd, qpart q (maxOrd p) = Qd := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, maxOrd p / Qd = B := ⟨_, rfl⟩
  have hAdvd : A ∣ ordModP a p := hAdef ▸ qpart_dvd q (ordModP a p)
  have hApos : 0 < A := hAdef ▸ qpart_pos q (ordModP a p) hq2
  have hQddvd : Qd ∣ maxOrd p := hQddef ▸ qpart_dvd q (maxOrd p)
  have hQdpos : 0 < Qd := hQddef ▸ qpart_pos q (maxOrd p) hq2
  have hQdB : Qd * B = maxOrd p := by rw [← hBdef]; exact mul_div_cancel_of_dvd Qd (maxOrd p) hQdpos hQddvd
  have hBpos : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | hp'
    · exfalso; rw [h0, Nat.mul_zero] at hQdB; rw [← hQdB] at hdpos; exact absurd hdpos (Nat.lt_irrefl 0)
    · exact hp'
  -- x of order A,  y of order B
  obtain ⟨x, hxdef⟩ : ∃ x, (a ^ (ordModP a p / A)) % p = x := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, (g ^ (qpart q (maxOrd p))) % p = y := ⟨_, rfl⟩
  have hx0 : 0 < x := by
    rw [← hxdef]; exact Nat.pos_of_ne_zero (fun h0 =>
      not_dvd_pow a p (ordModP a p / A) hp hpr hna (E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero h0))
  have hxlt : x < p := by rw [← hxdef]; exact Nat.mod_lt _ hppos
  have hy0 : 0 < y := by
    rw [← hydef]; exact Nat.pos_of_ne_zero (fun h0 =>
      not_dvd_pow g p (qpart q (maxOrd p)) hp hpr hng (E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero h0))
  have hylt : y < p := by rw [← hydef]; exact Nat.mod_lt _ hppos
  have hordx : ordModP x p = A := by
    rw [← hxdef, ← ord_mod_eq (a ^ (ordModP a p / A)) p]
    exact ord_pow_eq_of_dvd a p A hp hpr ha0 halt hAdvd
  have hQdord : Qd ∣ ordModP g p := by rw [hgmax]; exact hQddvd
  have hordy : ordModP y p = B := by
    rw [← hydef, hQddef, ← ord_mod_eq (g ^ Qd) p,
        ord_pow_div g p Qd hp hpr hg0 hglt hQdpos hQdord, hgmax, hBdef]
  -- gcd(A, B) = 1  (A = qᵉ, B q-free)
  have hqB : ¬ q ∣ B := by rw [← hBdef, ← hQddef]; exact q_not_dvd_quot q (maxOrd p) hq2 hdpos
  have hco : gcd213 (ordModP x p) (ordModP y p) = 1 := by
    rw [hordx, hordy, ← hAdef]
    show gcd213 (q ^ vp q (ordModP a p)) B = 1
    exact gcd_qpow_qfree q (vp q (ordModP a p)) B hq2 hqpr hqB
  -- ord((x·y)%p) = A·B
  have hordxy : ordModP ((x * y) % p) p = A * B := by
    rw [ord_mul_coprime x y p hp hpr hx0 hxlt hy0 hylt hco, hordx, hordy]
  -- A·B ≥ q·d > d
  have hAge : Qd * q ≤ A := by
    rw [← hAdef, ← hQddef]   -- A = q^(vp q (ord a)), Qd = q^(vp q d)
    show q ^ vp q (maxOrd p) * q ≤ q ^ vp q (ordModP a p)
    calc q ^ vp q (maxOrd p) * q = q ^ (vp q (maxOrd p) + 1) := by rw [Nat.pow_succ]
      _ ≤ q ^ vp q (ordModP a p) :=
        Nat.pow_le_pow_right (Nat.le_trans (by decide) hq2) hvgt
  have hABge : maxOrd p * q ≤ A * B := by
    calc maxOrd p * q = (Qd * B) * q := by rw [hQdB]
      _ = (Qd * q) * B := by ring_nat
      _ ≤ A * B := Nat.mul_le_mul_right B hAge
  have hABgt : maxOrd p < A * B := by
    have hdq : maxOrd p < maxOrd p * q := by
      have h2 : maxOrd p * 2 ≤ maxOrd p * q := Nat.mul_le_mul (Nat.le_refl _) hq2
      have h1 : maxOrd p < maxOrd p * 2 := by rw [Nat.mul_two]; exact Nat.lt_add_of_pos_right hdpos
      exact Nat.lt_of_lt_of_le h1 h2
    exact Nat.lt_of_lt_of_le hdq hABge
  -- but (x·y)%p is a unit ⟹ ord ≤ maxOrd
  have hxy0 : 0 < (x * y) % p := Nat.pos_of_ne_zero (fun h0 =>
    (nat_prime_dvd_mul p hp hpr x y (E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero h0)).elim
      (fun hpx => absurd (le_of_dvd_pos p x hx0 hpx) (Nat.not_le.mpr hxlt))
      (fun hpy => absurd (le_of_dvd_pos p y hy0 hpy) (Nat.not_le.mpr hylt)))
  have hxylt : (x * y) % p < p := Nat.mod_lt _ hppos
  have hxyle : (x * y) % p ≤ p - 1 := Nat.le_sub_one_of_lt hxylt
  have hle : ordModP ((x * y) % p) p ≤ maxOrd p := maxOrd_ge p ((x * y) % p) hxy0 hxyle
  rw [hordxy] at hle
  exact absurd hle (Nat.not_le.mpr hABgt)

end E213.Lib.Math.NumberTheory.ModArith.EveryOrdDvdMax
