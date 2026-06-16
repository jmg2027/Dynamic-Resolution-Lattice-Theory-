import E213.Lib.Math.NumberTheory.OddPartDecomposition
import E213.Lib.Math.NumberTheory.MobiusDivisorSum
import E213.Meta.Tactic.Pow213
import E213.Meta.Nat.Iterate213

/-!
# Coprime-square-split + square-or-twice-square ⟺ oddPart-square (∅-axiom)

Advances the σ-parity programme (square characterization via the odd-part
decomposition; the programme is closed in `SigmaParityComplete`).

`IsSquare n := ∃ r, r*r = n` (over `Nat`).

★★★ `coprime_isSquare_mul (h : gcd213 u v = 1) :
        IsSquare (u*v) ↔ (IsSquare u ∧ IsSquare v)`
    — fully GENERAL `→` via the gcd route (no UFD): `gcd(u,r)² = u`.

★★ `isSquare_two_pow_iff : IsSquare (2^a) ↔ a % 2 = 0`.

★★ `isSquare_iff (hn : 0 < n) :
        IsSquare n ↔ (v2 n % 2 = 0 ∧ IsSquare (oddPart n))`.

★★★ `sq_or_twice_iff (hn : 0 < n) :
        ((∃ r, r*r = n) ∨ (∃ r, 2*(r*r) = n)) ↔ IsSquare (oddPart n)`.
-/

namespace E213.Lib.Math.NumberTheory.SquareCharacterization

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd_strip_coprime
   coprime_dvd_of_dvd_mul dvd_antisymm_213 gcd213_comm gcd213_mul_left)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
  (coprime_mul_of_coprime coprime_pow_right dvd_trans_213)
open E213.Meta.Nat.NatDiv213 (mul_mod_self_pure)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Lib.Math.NumberTheory.OddPartDecomposition
  (v2 oddPart decomp oddPart_odd oddPart_pos coprime_two_pow_oddPart)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum (divisor_of_prime_pow_eq)
open E213.Lib.Math.NumberTheory.FactorialLcmDvd (prime2)
open E213.Meta.Nat.Iterate213 (pow_pow_eq_pow_mul pow_add_from_iter)
open E213.Tactic.Pow213 (pow_lt_pow_two)

/-- `IsSquare n := ∃ r, r*r = n`. -/
def IsSquare (n : Nat) : Prop := ∃ r, r * r = n

/-! ## §1 — coprime-square-split -/

/-- The `←` content packed as a divisibility/coprimality step: if `gcd(u,v)=1`
    and `u*v = r*r`, then `u = (gcd213 u r)²`.  No UFD: pure gcd machinery. -/
theorem isSquare_left_of_coprime_mul_eq_sq
    {u v r : Nat} (hco : gcd213 u v = 1) (h : u * v = r * r) :
    u = gcd213 u r * gcd213 u r := by
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · -- u = 0 ⟹ gcd(0,r)=r, but then u*v=0=r*r ⟹ r=0; both sides 0.
    subst hu0
    rw [Nat.zero_mul] at h
    -- 0 = r*r ⟹ r = 0
    have hr0 : r = 0 := by
      rcases Nat.eq_zero_or_pos r with h0 | hp
      · exact h0
      · exact absurd h.symm (Nat.ne_of_gt (Nat.mul_pos hp hp))
    show (0 : Nat) = gcd213 0 r * gcd213 0 r
    rw [hr0]; decide
  · -- u > 0, so d := gcd213 u r > 0.
    have hdu : gcd213 u r ∣ u := gcd213_dvd_left u r
    have hdr : gcd213 u r ∣ r := gcd213_dvd_right u r
    have hdpos : 0 < gcd213 u r := by
      rcases Nat.eq_zero_or_pos (gcd213 u r) with h0 | hp
      · obtain ⟨c, hc⟩ := hdu
        rw [h0, Nat.zero_mul] at hc
        exact absurd (hc ▸ hupos) (Nat.lt_irrefl 0)
      · exact hp
    obtain ⟨a, ha⟩ := hdu          -- u = d * a
    obtain ⟨b, hb⟩ := hdr          -- r = d * b
    have hcoab : gcd213 a b = 1 := gcd_strip_coprime (rfl) hdpos ha hb
    -- u*v = r*r  ⟹  d*a*v = d*d*(b*b)  ⟹  a*v = d*(b*b)
    have hdu2 : gcd213 u r ∣ u := ⟨a, ha⟩
    have hkey : a * v = gcd213 u r * (b * b) := by
      have h1 : gcd213 u r * (a * v) = gcd213 u r * (gcd213 u r * (b * b)) := by
        calc gcd213 u r * (a * v)
            = (gcd213 u r * a) * v := by rw [E213.Tactic.NatHelper.mul_assoc]
          _ = u * v := by rw [← ha]
          _ = r * r := h
          _ = (gcd213 u r * b) * (gcd213 u r * b) := by rw [← hb]
          _ = gcd213 u r * (gcd213 u r * (b * b)) := by ring_nat
      exact Nat.eq_of_mul_eq_mul_left hdpos h1
    -- a ∣ d :  a ∣ a*v = d*(b*b); gcd(a, b*b)=1 ⟹ a ∣ d.
    have hcoabb : gcd213 a (b * b) = 1 := coprime_mul_of_coprime hcoab hcoab
    have hadvd : a ∣ gcd213 u r := by
      have hdvd : a ∣ (b * b) * gcd213 u r :=
        ⟨v, by rw [Nat.mul_comm (b * b) (gcd213 u r)]; exact hkey.symm⟩
      exact coprime_dvd_of_dvd_mul hcoabb hdvd
    -- d ∣ a :  gcd(d,v)=1 (d∣u, gcd(u,v)=1); d ∣ a*v = d*(b*b) ⟹ d ∣ a.
    have hcodv : gcd213 (gcd213 u r) v = 1 := by
      have hh : gcd213 (gcd213 u r) v ∣ gcd213 u v := by
        refine gcd213_greatest u v (gcd213 (gcd213 u r) v) ?_
          (gcd213_dvd_right (gcd213 u r) v)
        exact dvd_trans_213 (gcd213_dvd_left (gcd213 u r) v) hdu2
      have hdvd1 : gcd213 (gcd213 u r) v ∣ 1 := hco ▸ hh
      obtain ⟨c, hc⟩ := hdvd1
      exact E213.Meta.Nat.Gcd213.mul_eq_one_left _ c hc.symm
    have hdadvd : gcd213 u r ∣ a := by
      have hdvd : gcd213 u r ∣ v * a := ⟨b * b, by rw [Nat.mul_comm v a, hkey]⟩
      exact coprime_dvd_of_dvd_mul hcodv hdvd
    have had : a = gcd213 u r := dvd_antisymm_213 a (gcd213 u r) hadvd hdadvd
    calc u = gcd213 u r * a := ha
      _ = gcd213 u r * gcd213 u r := by rw [had]

/-- ★★★ **Coprime-square-split** (GENERAL): for coprime `u,v`,
    `IsSquare (u*v) ↔ IsSquare u ∧ IsSquare v`. -/
theorem coprime_isSquare_mul {u v : Nat} (h : gcd213 u v = 1) :
    IsSquare (u * v) ↔ (IsSquare u ∧ IsSquare v) := by
  constructor
  · rintro ⟨r, hr⟩
    -- u is a square via the gcd route; v symmetrically (gcd v u = 1).
    have hu : u = gcd213 u r * gcd213 u r :=
      isSquare_left_of_coprime_mul_eq_sq h hr.symm
    have hco' : gcd213 v u = 1 := (gcd213_comm v u).trans h
    have hr' : v * u = r * r := by rw [Nat.mul_comm v u]; exact hr.symm
    have hv : v = gcd213 v r * gcd213 v r :=
      isSquare_left_of_coprime_mul_eq_sq hco' hr'
    exact ⟨⟨gcd213 u r, hu.symm⟩, ⟨gcd213 v r, hv.symm⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a * b, by rw [← ha, ← hb]; ring_nat⟩

/-! ## §2 — `IsSquare (2^a) ↔ a even` -/

/-- `IsSquare (2^a) ↔ a % 2 = 0`. -/
theorem isSquare_two_pow_iff (a : Nat) : IsSquare (2 ^ a) ↔ a % 2 = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    -- r ∣ 2^a, r > 0, so r = 2^(vp 2 r) =: 2^k.
    have hrpos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | hp
      · rw [h0, Nat.zero_mul] at hr
        exact absurd hr.symm (Nat.ne_of_gt (Nat.pos_pow_of_pos a (by decide)))
      · exact hp
    have hrdvd : r ∣ 2 ^ a := ⟨r, hr.symm⟩
    have hrpow : r = 2 ^ (E213.Meta.Nat.Valuation.vp 2 r) :=
      divisor_of_prime_pow_eq prime2 hrpos hrdvd
    -- 2^a = r*r = 2^k * 2^k = 2^(k+k); so a = k + k = 2k  (k := vp 2 r).
    have hpow : (2 : Nat) ^ a
        = 2 ^ (E213.Meta.Nat.Valuation.vp 2 r + E213.Meta.Nat.Valuation.vp 2 r) := by
      rw [pow_add_from_iter, ← hrpow]
      exact hr.symm
    have hak : a = E213.Meta.Nat.Valuation.vp 2 r + E213.Meta.Nat.Valuation.vp 2 r := by
      rcases Nat.lt_trichotomy a (E213.Meta.Nat.Valuation.vp 2 r
          + E213.Meta.Nat.Valuation.vp 2 r) with hlt | heq | hgt
      · exact absurd (hpow ▸ pow_lt_pow_two _ _ hlt) (Nat.lt_irrefl _)
      · exact heq
      · exact absurd (hpow.symm ▸ pow_lt_pow_two _ _ hgt) (Nat.lt_irrefl _)
    rw [hak]
    -- (k+k) % 2 = 0
    rw [show E213.Meta.Nat.Valuation.vp 2 r + E213.Meta.Nat.Valuation.vp 2 r
        = 2 * E213.Meta.Nat.Valuation.vp 2 r from by ring_nat]
    exact mul_mod_self_pure 2 (E213.Meta.Nat.Valuation.vp 2 r)
  · intro ha
    -- a = 2*(a/2): build the witness 2^(a/2).
    obtain ⟨m, hm⟩ : ∃ m, a = 2 * m := by
      refine ⟨a / 2, ?_⟩
      have hdm : 2 * (a / 2) + a % 2 = a := div_add_mod a 2
      rw [ha, Nat.add_zero] at hdm
      exact hdm.symm
    refine ⟨2 ^ m, ?_⟩
    rw [← pow_add_from_iter, hm]
    rw [show m + m = 2 * m from by ring_nat]

/-! ## §3 — bridges to the odd part -/

open E213.Lib.Math.NumberTheory.OddPartDecomposition (stripTwo stripTwo_two_mul)

/-- `v2 (2*k) = v2 k + 1` for `k > 0`. -/
theorem v2_two_mul {k : Nat} (hk : 0 < k) : v2 (2 * k) = v2 k + 1 := by
  show (stripTwo (2 * k + 1) (2 * k)).1 = (stripTwo (k + 1) k).1 + 1
  rw [stripTwo_two_mul (f := 2 * k) hk (Nat.le_succ _)]

/-- `oddPart (2*k) = oddPart k` for `k > 0`. -/
theorem oddPart_two_mul {k : Nat} (hk : 0 < k) : oddPart (2 * k) = oddPart k := by
  show (stripTwo (2 * k + 1) (2 * k)).2 = (stripTwo (k + 1) k).2
  rw [stripTwo_two_mul (f := 2 * k) hk (Nat.le_succ _)]

/-- Product of two squares is a square. -/
theorem isSquare_mul {a b : Nat} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a * b) := by
  obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb
  exact ⟨x * y, by rw [← hx, ← hy]; ring_nat⟩

/-- ★★ **Square ⟺ `v2` even ∧ `oddPart` square** (from the coprime split + decomp). -/
theorem isSquare_iff {n : Nat} (hn : 0 < n) :
    IsSquare n ↔ (v2 n % 2 = 0 ∧ IsSquare (oddPart n)) := by
  have hco := coprime_two_pow_oddPart hn
  constructor
  · intro hsq
    rw [decomp hn] at hsq
    have hpair := (coprime_isSquare_mul hco).mp hsq
    exact ⟨(isSquare_two_pow_iff (v2 n)).mp hpair.1, hpair.2⟩
  · rintro ⟨hv, hop⟩
    rw [decomp hn]
    exact (coprime_isSquare_mul hco).mpr ⟨(isSquare_two_pow_iff (v2 n)).mpr hv, hop⟩

/-- `e` even ⟹ `e+1` odd. -/
theorem succ_mod_two_of_even {e : Nat} (h : e % 2 = 0) : (e + 1) % 2 = 1 := by
  rw [E213.Meta.Nat.AddMod213.add_mod (by decide) e 1, h]

/-- ★★ **Twice-a-square ⟺ `v2` odd ∧ `oddPart` square**. -/
theorem twiceSquare_iff {n : Nat} (hn : 0 < n) :
    (∃ r, 2 * (r * r) = n) ↔ (v2 n % 2 = 1 ∧ IsSquare (oddPart n)) := by
  constructor
  · rintro ⟨r, hr⟩
    have hrr : 0 < r * r := by
      rcases Nat.eq_zero_or_pos (r * r) with h0 | hp
      · rw [h0, Nat.mul_zero] at hr; exact absurd hr (Nat.ne_of_lt hn)
      · exact hp
    have hchar := (isSquare_iff hrr).mp ⟨r, rfl⟩
    subst hr
    rw [v2_two_mul hrr, oddPart_two_mul hrr]
    exact ⟨succ_mod_two_of_even hchar.1, hchar.2⟩
  · rintro ⟨hv, hop⟩
    obtain ⟨t, ht⟩ : ∃ t, v2 n = 2 * t + 1 := by
      refine ⟨v2 n / 2, ?_⟩
      have hd := E213.Meta.Nat.AddMod213.div_add_mod (v2 n) 2
      rw [hv] at hd; exact hd.symm
    obtain ⟨s, hs⟩ := hop
    have e1 : (2 : Nat) ^ (2 * t) = 2 ^ t * 2 ^ t := by
      rw [show 2 * t = t + t from by ring_nat, pow_add_from_iter]
    have e2 : (2 : Nat) ^ (2 * t + 1) = 2 ^ (2 * t) * 2 := by rw [pow_add_from_iter]
    refine ⟨2 ^ t * s, ?_⟩
    rw [decomp hn, ht, e2, e1, ← hs]
    ring_nat

/-- ★★★ **Square-or-twice-square ⟺ `oddPart` square** — the σ-parity bridge. -/
theorem sq_or_twice_iff {n : Nat} (hn : 0 < n) :
    ((∃ r, r * r = n) ∨ (∃ r, 2 * (r * r) = n)) ↔ IsSquare (oddPart n) := by
  constructor
  · rintro (hsq | htw)
    · exact ((isSquare_iff hn).mp hsq).2
    · exact ((twiceSquare_iff hn).mp htw).2
  · intro hop
    rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one (v2 n) with he | ho
    · exact Or.inl ((isSquare_iff hn).mpr ⟨he, hop⟩)
    · exact Or.inr ((twiceSquare_iff hn).mpr ⟨ho, hop⟩)

end E213.Lib.Math.NumberTheory.SquareCharacterization
