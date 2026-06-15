import E213.Meta.Nat.Gcd213

/-!
# Coprimality is multiplicative (∅-axiom, general `a b c : Nat`)

`gcd(a, b·c) = 1  ↔  gcd(a,b) = 1 ∧ gcd(a,c) = 1`.

This is THE foundational lemma behind the multiplicativity of every arithmetic
function (Euler `φ`, Möbius `μ`, divisor-count `τ`, divisor-sum `σ`): each is
multiplicative *because* coprime factorizations split, and they split *because*
coprimality splits across a product.  Proven for arbitrary `a, b, c` from the
repo's ∅-axiom gcd kernel (`gcd213`) — Euclid's lemma
(`coprime_dvd_of_dvd_mul`), `gcd213_greatest`, `gcd213_dvd_left/right`.

Absent from the corpus: only `ord_mul_coprime` (a *consequence* about
multiplicative orders) and `gcd_mul_lcm` existed; the general split of
coprimality across a product is new here.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest
   mul_eq_one_left coprime_dvd_of_dvd_mul mul_assoc_213)

/-- `d ∣ 1 → d = 1` (∅-axiom; from `mul_eq_one_left`). -/
theorem eq_one_of_dvd_one {d : Nat} (h : d ∣ 1) : d = 1 := by
  obtain ⟨c, hc⟩ := h
  exact mul_eq_one_left d c hc.symm

/-- Divisibility is transitive (∅-axiom; `Dvd.dvd.trans` needs Mathlib). -/
theorem dvd_trans_213 {a b c : Nat} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  exact ⟨x * y, by rw [hy, hx, mul_assoc_213]⟩

/-- Forward, left factor: `gcd(a, b·c) = 1 → gcd(a,b) = 1`.
    `gcd(a,b)` divides `a` and `b`, hence `b·c`, hence `gcd(a,b·c) = 1`. -/
theorem coprime_of_coprime_mul_left {a b c : Nat}
    (h : gcd213 a (b * c) = 1) : gcd213 a b = 1 := by
  have hda : gcd213 a b ∣ a := gcd213_dvd_left a b
  have hdb : gcd213 a b ∣ b := gcd213_dvd_right a b
  have hbc : gcd213 a b ∣ b * c := dvd_trans_213 hdb ⟨c, rfl⟩
  have hdg : gcd213 a b ∣ gcd213 a (b * c) :=
    gcd213_greatest a (b * c) (gcd213 a b) hda hbc
  exact eq_one_of_dvd_one (h ▸ hdg)

/-- Forward, right factor: `gcd(a, b·c) = 1 → gcd(a,c) = 1`. -/
theorem coprime_of_coprime_mul_right {a b c : Nat}
    (h : gcd213 a (b * c) = 1) : gcd213 a c = 1 :=
  coprime_of_coprime_mul_left (a := a) (b := c) (c := b)
    (by rw [Nat.mul_comm c b]; exact h)

/-- Backward: `gcd(a,b) = 1 → gcd(a,c) = 1 → gcd(a, b·c) = 1`.
    Let `g = gcd(a, b·c)`.  `g ∣ a`, so `gcd(g,b) ∣ gcd(a,b) = 1`, i.e. `g`
    is coprime to `b`; with `g ∣ b·c`, Euclid gives `g ∣ c`.  Then
    `g ∣ gcd(a,c) = 1`, so `g = 1`. -/
theorem coprime_mul_of_coprime {a b c : Nat}
    (hb : gcd213 a b = 1) (hc : gcd213 a c = 1) : gcd213 a (b * c) = 1 := by
  have hga : gcd213 a (b * c) ∣ a := gcd213_dvd_left a (b * c)
  have hgbc : gcd213 a (b * c) ∣ b * c := gcd213_dvd_right a (b * c)
  -- g coprime to b:  gcd(g,b) ∣ a and ∣ b, hence ∣ gcd(a,b) = 1
  have hgb1 : gcd213 (gcd213 a (b * c)) b = 1 := by
    have hd_a : gcd213 (gcd213 a (b * c)) b ∣ a :=
      dvd_trans_213 (gcd213_dvd_left (gcd213 a (b * c)) b) hga
    have hd_b : gcd213 (gcd213 a (b * c)) b ∣ b :=
      gcd213_dvd_right (gcd213 a (b * c)) b
    have : gcd213 (gcd213 a (b * c)) b ∣ gcd213 a b :=
      gcd213_greatest a b _ hd_a hd_b
    exact eq_one_of_dvd_one (hb ▸ this)
  -- Euclid: g ∣ b·c and gcd(g,b)=1  ⟹  g ∣ c
  have hgc : gcd213 a (b * c) ∣ c := coprime_dvd_of_dvd_mul hgb1 hgbc
  -- g ∣ gcd(a,c) = 1
  have : gcd213 a (b * c) ∣ gcd213 a c :=
    gcd213_greatest a c _ hga hgc
  exact eq_one_of_dvd_one (hc ▸ this)

/-- ★ **Coprimality is multiplicative** (general `a b c : Nat`):
    `gcd(a, b·c) = 1 ↔ gcd(a,b) = 1 ∧ gcd(a,c) = 1`.
    The structural reason arithmetic functions are multiplicative. -/
theorem coprime_mul_iff (a b c : Nat) :
    gcd213 a (b * c) = 1 ↔ gcd213 a b = 1 ∧ gcd213 a c = 1 :=
  Iff.intro
    (fun h => ⟨coprime_of_coprime_mul_left h, coprime_of_coprime_mul_right h⟩)
    (fun ⟨hb, hc⟩ => coprime_mul_of_coprime hb hc)

/-- Concrete sanity checks: `35 = 5·7` is coprime to `12`, not to `15`. -/
theorem coprime_mul_smoke :
    gcd213 35 (3 * 4) = 1 ∧ ¬ gcd213 35 (3 * 5) = 1 := by
  refine ⟨by decide, by decide⟩

end E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
