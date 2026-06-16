import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.NatDiv213
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Tactic.Pow213
import E213.Meta.Nat.PolyNatMTactic

/-!
# Lcm213 — the least common multiple over `ℕ`, ∅-axiom

`lcm213 a b = a · b / gcd a b`.  The universal property `a ∣ m ∧ b ∣ m ⟹ lcm ∣ m` is proved
**without Bezout**: writing `lcm = a · (b/g)` and `m = a · u`, it reduces to `(b/g) ∣ u`, which
follows from `gcd(a/g, b/g) = 1` (`gcd_div_coprime`) + Euclid's lemma
(`MarkovPrimeFactor.euclid_of_coprime`).

  * `dvd_lcm_left` / `dvd_lcm_right` — `a ∣ lcm`, `b ∣ lcm`.
  * ★★★ `lcm_dvd` — `a ∣ m → b ∣ m → lcm ∣ m` (the universal property).
  * `lcm_pos`, `gcd_mul_lcm` (`g · lcm = a · b`).

The foundation toward primitive roots (`(ℤ/p)*` cyclic, via the exponent argument).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.Lcm213

open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure mul_div_self_pure)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (euclid_of_coprime)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Tactic.NatHelper (gcd213)

/-- The least common multiple: `a · b / gcd a b`. -/
def lcm213 (a b : Nat) : Nat := a * b / gcd213 a b

/-! ## §1 — gcd positivity + a div-cancellation helper -/

/-- `gcd a b > 0` when `a > 0` (the gcd divides `a`). -/
theorem gcd_pos (a b : Nat) (ha : 0 < a) : 0 < gcd213 a b := by
  rcases Nat.eq_zero_or_pos (gcd213 a b) with h0 | hpos
  · obtain ⟨c, hc⟩ := gcd213_dvd_left a b
    rw [h0, Nat.zero_mul] at hc; rw [hc] at ha; exact absurd ha (Nat.lt_irrefl 0)
  · exact hpos

/-- `g ∣ x ⟹ g · (x / g) = x` (`g > 0`). -/
theorem mul_div_cancel_of_dvd (g x : Nat) (hg : 0 < g) (h : g ∣ x) : g * (x / g) = x := by
  obtain ⟨c, hc⟩ := h
  rw [hc, mul_div_cancel_left_pure g c hg]

/-! ## §2 — `gcd(a/g, b/g) = 1` -/

/-- ★★ **The gcd-reduced parts are coprime**: `gcd(a/g, b/g) = 1` for `g = gcd a b` (`a,b > 0`). -/
theorem gcd_div_coprime (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    gcd213 (a / gcd213 a b) (b / gcd213 a b) = 1 := by
  obtain ⟨g, hgdef⟩ : ∃ g, gcd213 a b = g := ⟨_, rfl⟩
  have hg : 0 < g := hgdef ▸ gcd_pos a b ha
  have hga : g ∣ a := hgdef ▸ gcd213_dvd_left a b
  have hgb : g ∣ b := hgdef ▸ gcd213_dvd_right a b
  rw [hgdef]
  -- let d = gcd (a/g) (b/g); show d = 1 by d·g ∣ g
  obtain ⟨d, hddef⟩ : ∃ d, gcd213 (a / g) (b / g) = d := ⟨_, rfl⟩
  rw [hddef]
  have hda : d ∣ (a / g) := hddef ▸ gcd213_dvd_left (a / g) (b / g)
  have hdb : d ∣ (b / g) := hddef ▸ gcd213_dvd_right (a / g) (b / g)
  -- d·g ∣ a and d·g ∣ b
  have hdga : d * g ∣ a := by
    obtain ⟨e, he⟩ := hda
    refine ⟨e, ?_⟩
    have : g * (a / g) = a := mul_div_cancel_of_dvd g a hg hga
    rw [← this, he]; ring_nat
  have hdgb : d * g ∣ b := by
    obtain ⟨e, he⟩ := hdb
    refine ⟨e, ?_⟩
    have : g * (b / g) = b := mul_div_cancel_of_dvd g b hg hgb
    rw [← this, he]; ring_nat
  have hdgg : d * g ∣ g := hgdef ▸ gcd213_greatest a b (d * g) hdga hdgb
  -- d·g ≤ g ⟹ d ≤ 1; and d ≥ 1 (gcd of positives) ⟹ d = 1
  have hle : d * g ≤ g := le_of_dvd_pos (d * g) g hg hdgg
  have hd1 : d ≤ 1 := by
    rcases Nat.lt_or_ge d 2 with h2 | h2
    · exact Nat.le_of_lt_succ h2
    · exfalso
      have hge : 2 * g ≤ d * g := Nat.mul_le_mul h2 (Nat.le_refl g)
      have hgg : g + g ≤ d * g := by rw [show 2 * g = g + g from by ring_nat] at hge; exact hge
      have hg1 : g + 1 ≤ g + g := Nat.add_le_add_left hg g
      exact absurd (Nat.le_trans (Nat.le_trans hg1 hgg) hle) (Nat.not_succ_le_self g)
  have hagp : 0 < a / g := by
    rcases Nat.eq_zero_or_pos (a / g) with h0 | hp
    · exfalso
      have hga' := mul_div_cancel_of_dvd g a hg hga
      rw [h0, Nat.mul_zero] at hga'
      rw [← hga'] at ha; exact absurd ha (Nat.lt_irrefl 0)
    · exact hp
  have hdpos : 0 < d := hddef ▸ gcd_pos (a / g) (b / g) hagp
  exact Nat.le_antisymm hd1 hdpos

/-! ## §3 — `lcm = a·(b/g) = (a/g)·b` -/

theorem lcm_eq_left (a b : Nat) (ha : 0 < a) :
    lcm213 a b = a * (b / gcd213 a b) := by
  obtain ⟨g, hgdef⟩ : ∃ g, gcd213 a b = g := ⟨_, rfl⟩
  have hg : 0 < g := hgdef ▸ gcd_pos a b ha
  have hgb : g ∣ b := hgdef ▸ gcd213_dvd_right a b
  obtain ⟨q, hq⟩ : ∃ q, b / g = q := ⟨_, rfl⟩
  have hbg : g * q = b := by rw [← hq]; exact mul_div_cancel_of_dvd g b hg hgb
  show a * b / gcd213 a b = a * (b / gcd213 a b)
  rw [hgdef, hq, ← hbg, show a * (g * q) = a * q * g from by ring_nat,
      mul_div_self_pure (a * q) g hg]

theorem lcm_eq_right (a b : Nat) (hb : 0 < b) :
    lcm213 a b = (a / gcd213 a b) * b := by
  obtain ⟨g, hgdef⟩ : ∃ g, gcd213 a b = g := ⟨_, rfl⟩
  have hg : 0 < g := hgdef ▸ (gcd213_comm a b ▸ gcd_pos b a hb)
  have hga : g ∣ a := hgdef ▸ gcd213_dvd_left a b
  obtain ⟨p, hp⟩ : ∃ p, a / g = p := ⟨_, rfl⟩
  have hag : g * p = a := by rw [← hp]; exact mul_div_cancel_of_dvd g a hg hga
  show a * b / gcd213 a b = (a / gcd213 a b) * b
  rw [hgdef, hp, ← hag, show g * p * b = p * b * g from by ring_nat,
      mul_div_self_pure (p * b) g hg]

/-! ## §4 — divisibility + universal property -/

theorem dvd_lcm_left (a b : Nat) (ha : 0 < a) : a ∣ lcm213 a b := by
  rw [lcm_eq_left a b ha]; exact ⟨b / gcd213 a b, rfl⟩

theorem dvd_lcm_right (a b : Nat) (hb : 0 < b) : b ∣ lcm213 a b := by
  rw [lcm_eq_right a b hb]; exact ⟨a / gcd213 a b, by rw [Nat.mul_comm]⟩

/-- ★★★ **The universal property of `lcm`**: every common multiple is a multiple of `lcm`.
    `m = a·u`, and `lcm = a·(b/g)`, so it reduces to `(b/g) ∣ u`; `b ∣ a·u` divided by `g` gives
    `(b/g) ∣ (a/g)·u`, and `gcd(b/g, a/g) = 1` + Euclid finishes. -/
theorem lcm_dvd (a b m : Nat) (ha : 0 < a) (hb : 0 < b) (hma : a ∣ m) (hmb : b ∣ m) :
    lcm213 a b ∣ m := by
  obtain ⟨g, hgdef⟩ : ∃ g, gcd213 a b = g := ⟨_, rfl⟩
  have hg : 0 < g := hgdef ▸ gcd_pos a b ha
  have hga : g ∣ a := hgdef ▸ gcd213_dvd_left a b
  have hgb : g ∣ b := hgdef ▸ gcd213_dvd_right a b
  obtain ⟨p, hp⟩ : ∃ p, a / g = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, b / g = q := ⟨_, rfl⟩
  have hag : g * p = a := by rw [← hp]; exact mul_div_cancel_of_dvd g a hg hga
  have hbg : g * q = b := by rw [← hq]; exact mul_div_cancel_of_dvd g b hg hgb
  obtain ⟨u, hu⟩ := hma            -- m = a * u
  -- goal: lcm ∣ m, i.e. a * q ∣ m
  rw [lcm_eq_left a b ha, hgdef, hq]
  -- reduce `a*q ∣ m` (with `m = a*u`) to `q ∣ u`
  have hqu : q ∣ u := by
    rcases Nat.lt_or_ge q 2 with hq2 | hq2
    · -- q ≤ 1
      have hq1 : q = 1 := by
        rcases Nat.lt_or_ge q 1 with h0 | h1
        · -- q = 0 impossible (b > 0)
          exfalso
          have hq0 : q = 0 := by
            rcases q with _ | k
            · rfl
            · exact absurd h0 (Nat.not_lt.mpr (Nat.succ_le_succ (Nat.zero_le k)))
          rw [hq0, Nat.mul_zero] at hbg; rw [← hbg] at hb; exact absurd hb (Nat.lt_irrefl 0)
        · exact Nat.le_antisymm (Nat.le_of_lt_succ hq2) h1
      rw [hq1]; exact Nat.one_dvd u
    · -- q ≥ 2: Euclid
      have hbau : b ∣ a * u := hu ▸ hmb
      -- g*q ∣ g*(p*u)  ⟹  q ∣ p*u
      have hgqdvd : g * q ∣ g * (p * u) := by
        obtain ⟨c, hc⟩ := hbau
        refine ⟨c, ?_⟩
        rw [hbg, ← hc, ← hag]; ring_nat
      have hqpu : q ∣ p * u := by
        obtain ⟨c, hc⟩ := hgqdvd
        refine ⟨c, ?_⟩
        have heq : g * (p * u) = g * (q * c) := by rw [hc]; ring_nat
        exact Nat.eq_of_mul_eq_mul_left hg heq
      have hco : gcd213 p q = 1 := by
        rw [← hp, ← hq, ← hgdef]; exact gcd_div_coprime a b ha hb
      exact euclid_of_coprime p u q hq2 hco hqpu
  obtain ⟨c, hc⟩ := hqu            -- u = q * c
  refine ⟨c, ?_⟩
  rw [hu, hc]; ring_nat

/-! ## §5 — positivity + the gcd·lcm identity -/

theorem lcm_pos (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < lcm213 a b := by
  rw [lcm_eq_left a b ha]
  have hgb : 0 < b / gcd213 a b := by
    rcases Nat.eq_zero_or_pos (b / gcd213 a b) with h0 | hpos
    · exfalso
      have := mul_div_cancel_of_dvd (gcd213 a b) b (gcd_pos a b ha) (gcd213_dvd_right a b)
      rw [h0, Nat.mul_zero] at this; rw [← this] at hb; exact absurd hb (Nat.lt_irrefl 0)
    · exact hpos
  exact Nat.mul_pos ha hgb

/-- `gcd · lcm = a · b`. -/
theorem gcd_mul_lcm (a b : Nat) (ha : 0 < a) : gcd213 a b * lcm213 a b = a * b := by
  obtain ⟨g, hgdef⟩ : ∃ g, gcd213 a b = g := ⟨_, rfl⟩
  have hg : 0 < g := hgdef ▸ gcd_pos a b ha
  have hgb : g ∣ b := hgdef ▸ gcd213_dvd_right a b
  obtain ⟨q, hq⟩ : ∃ q, b / g = q := ⟨_, rfl⟩
  have hbg : g * q = b := by rw [← hq]; exact mul_div_cancel_of_dvd g b hg hgb
  rw [lcm_eq_left a b ha, hgdef, hq, ← hbg]; ring_nat

/-- ★ Concrete: `lcm213 4 6 = 12` (= `4·6 / gcd213 4 6 = 24/2`).  Exercises the
    fuel-driven `gcd213`/`Nat.div` kernel reduction, ∅-axiom. -/
theorem lcm213_4_6 : lcm213 4 6 = 12 := by decide

end E213.Lib.Math.NumberTheory.Lcm213
