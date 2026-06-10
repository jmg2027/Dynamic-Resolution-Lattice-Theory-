import E213.Lib.Math.NumberTheory.ModArith.QPart
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.FourSquare
import E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
import E213.Meta.Nat.PolyNatMTactic

/-!
# ValuationAlg — `vp` is additive on products, and the prime-valuation extraction (brick 4b-iii)

  * ★ `vp_mul` — `vp q (a·b) = vp q a + vp q b` (`q` prime, `a,b > 0`).
  * ★★★ `exists_prime_vp_gt` — `α ∤ d` (both `> 0`) ⟹ `∃ q, (q prime) ∧ vp q α > vp q d`.

The extraction avoids `min`/full factorisation: a prime `q ∣ α/gcd(α,d)` cannot divide `d/gcd`
(they are coprime — brick 1's `gcd_div_coprime`), so `vp_q(d/g) = 0` ⟹ `vp(d) = vp(g)`, while
`vp(α) = vp(g) + vp(α/g) ≥ vp(g) + 1`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ValuationAlg

open E213.Meta.Nat.Valuation (vp pow_vp_dvd le_vp_iff drefl dtrans)
open E213.Lib.Math.NumberTheory.ModArith.QPart (qpart qpart_dvd qpart_pos q_not_dvd_quot)
open E213.Lib.Math.NumberTheory.Lcm213 (mul_div_cancel_of_dvd gcd_pos gcd_div_coprime)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest dvd_antisymm_213
  mul_assoc_213)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Lib.Math.NumberTheory.FourSquare (exists_prime_factor)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (pow_add_pure)
open E213.Tactic.NatHelper (gcd213)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- `qᵏ ∣ n` and `q^(k+1) ∤ n` pin `vp q n = k`. -/
theorem vp_eq_of (q n k : Nat) (hq : 2 ≤ q) (hn : 0 < n) (h1 : q ^ k ∣ n)
    (h2 : ¬ q ^ (k + 1) ∣ n) : vp q n = k :=
  Nat.le_antisymm
    (Nat.le_of_lt_succ (Nat.lt_of_not_le (fun hle => h2 ((le_vp_iff q n (k + 1) hq hn).mpr hle))))
    ((le_vp_iff q n k hq hn).mp h1)

/-- `vp q n = 0` when `q ∤ n`. -/
theorem vp_eq_zero (q n : Nat) (hq : 2 ≤ q) (hn : 0 < n) (h : ¬ q ∣ n) : vp q n = 0 := by
  rcases Nat.eq_zero_or_pos (vp q n) with h0 | hpos
  · exact h0
  · exfalso; apply h
    have hd : q ^ 1 ∣ n := (le_vp_iff q n 1 hq hn).mpr hpos
    rwa [Nat.pow_one] at hd

/-- `1 ≤ vp q n` when `q ∣ n`. -/
theorem one_le_vp (q n : Nat) (hq : 2 ≤ q) (hn : 0 < n) (h : q ∣ n) : 1 ≤ vp q n :=
  (le_vp_iff q n 1 hq hn).mp (by rw [Nat.pow_one]; exact h)

/-! ## §1 — `vp` is additive on products -/

/-- ★ **`vp q (a·b) = vp q a + vp q b`** for a prime `q` and `a, b > 0`. -/
theorem vp_mul (q a b : Nat) (hq : 2 ≤ q) (hpr : ∀ d, d ∣ q → d = 1 ∨ d = q)
    (ha : 0 < a) (hb : 0 < b) : vp q (a * b) = vp q a + vp q b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  -- opaque valuations + q-free cofactors
  obtain ⟨va, hva⟩ : ∃ x, vp q a = x := ⟨_, rfl⟩
  obtain ⟨vb, hvb⟩ : ∃ x, vp q b = x := ⟨_, rfl⟩
  obtain ⟨a', haq⟩ : ∃ a', a / qpart q a = a' := ⟨_, rfl⟩
  obtain ⟨b', hbq⟩ : ∃ b', b / qpart q b = b' := ⟨_, rfl⟩
  have hqa : ¬ q ∣ a' := haq ▸ q_not_dvd_quot q a hq ha
  have hqb : ¬ q ∣ b' := hbq ▸ q_not_dvd_quot q b hq hb
  have hae : q ^ va * a' = a := by
    rw [← hva, ← haq]; exact mul_div_cancel_of_dvd (qpart q a) a (qpart_pos q a hq) (qpart_dvd q a)
  have hbe : q ^ vb * b' = b := by
    rw [← hvb, ← hbq]; exact mul_div_cancel_of_dvd (qpart q b) b (qpart_pos q b hq) (qpart_dvd q b)
  rw [hva, hvb]
  apply vp_eq_of q (a * b) (va + vb) hq hab
  · refine ⟨a' * b', ?_⟩
    rw [pow_add_pure, ← hae, ← hbe]; ring_nat
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hcollapse : q ^ (va + vb) * (a' * b') = q ^ (va + vb) * (q * c) := by
      rw [show q ^ (va + vb) * (a' * b') = a * b from by rw [pow_add_pure, ← hae, ← hbe]; ring_nat,
          hc, show q ^ (va + vb + 1) = q ^ (va + vb) * q from by rw [pow_add_pure, Nat.pow_one]]
      ring_nat
    have hqab : q ∣ (a' * b') := ⟨c, Nat.eq_of_mul_eq_mul_left
      (Nat.pos_pow_of_pos _ (Nat.lt_of_lt_of_le (by decide) hq)) hcollapse⟩
    exact (nat_prime_dvd_mul q hq hpr a' b' hqab).elim hqa hqb

/-! ## §2 — the prime-valuation extraction -/

/-- ★★★ **`α ∤ d` ⟹ `∃ prime q, vp q α > vp q d`** (both `> 0`).  A prime `q ∣ α/gcd(α,d)` is
    coprime to `d/gcd` (`gcd_div_coprime`), so `vp(d/g) = 0`; `vp(α) = vp(g) + vp(α/g) ≥ vp(g)+1`
    and `vp(d) = vp(g) + 0`. -/
theorem exists_prime_vp_gt (α d : Nat) (hα : 0 < α) (hd : 0 < d) (hnd : ¬ α ∣ d) :
    ∃ q, 1 < q ∧ (∀ e, e ∣ q → e = 1 ∨ e = q) ∧ vp q α > vp q d := by
  obtain ⟨g, hgdef⟩ : ∃ g, gcd213 α d = g := ⟨_, rfl⟩
  have hgpos : 0 < g := hgdef ▸ gcd_pos α d hα
  have hgα : g ∣ α := hgdef ▸ gcd213_dvd_left α d
  have hgd : g ∣ d := hgdef ▸ gcd213_dvd_right α d
  obtain ⟨Ag, hAg⟩ : ∃ x, α / g = x := ⟨_, rfl⟩
  obtain ⟨Dg, hDg⟩ : ∃ x, d / g = x := ⟨_, rfl⟩
  have hgAg : g * Ag = α := by rw [← hAg]; exact mul_div_cancel_of_dvd g α hgpos hgα
  have hgDg : g * Dg = d := by rw [← hDg]; exact mul_div_cancel_of_dvd g d hgpos hgd
  have hAgpos : 0 < Ag := by
    rcases Nat.eq_zero_or_pos Ag with h0 | hp
    · rw [h0, Nat.mul_zero] at hgAg; rw [← hgAg] at hα; exact absurd hα (Nat.lt_irrefl 0)
    · exact hp
  have hDgpos : 0 < Dg := by
    rcases Nat.eq_zero_or_pos Dg with h0 | hp
    · rw [h0, Nat.mul_zero] at hgDg; rw [← hgDg] at hd; exact absurd hd (Nat.lt_irrefl 0)
    · exact hp
  -- α/g ≥ 2  (else α/g = 1 ⟹ α = g = gcd(α,d) ⟹ α ∣ d)
  have hAg2 : 2 ≤ Ag := by
    rcases Nat.lt_or_ge Ag 2 with hlt | hge
    · exfalso
      have hAg1 : Ag = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hAgpos
      rw [hAg1, Nat.mul_one] at hgAg   -- g = α
      exact hnd (hgAg ▸ hgd)            -- α = g ∣ d
    · exact hge
  -- a prime q ∣ α/g = Ag
  obtain ⟨q, hq1, hqpr, hqAg⟩ := exists_prime_factor Ag Ag (Nat.le_refl _) hAg2
  have hq2 : 2 ≤ q := hq1
  -- q ∤ Dg  (Ag, Dg coprime)
  have hcop : gcd213 Ag Dg = 1 := by rw [← hAg, ← hDg, ← hgdef]; exact gcd_div_coprime α d hα hd
  have hqDg : ¬ q ∣ Dg := by
    intro hqd
    have hqg : q ∣ gcd213 Ag Dg := gcd213_greatest Ag Dg q hqAg hqd
    rw [hcop] at hqg
    exact absurd (le_of_dvd_pos q 1 (by decide) hqg) (Nat.not_le.mpr hq1)
  refine ⟨q, hq1, hqpr, ?_⟩
  -- vp q α = vp q g + vp q Ag ≥ vp q g + 1;  vp q d = vp q g + 0
  have hvα : vp q α = vp q g + vp q Ag := by rw [← hgAg]; exact vp_mul q g Ag hq2 hqpr hgpos hAgpos
  have hvd : vp q d = vp q g + vp q Dg := by rw [← hgDg]; exact vp_mul q g Dg hq2 hqpr hgpos hDgpos
  have hvDg0 : vp q Dg = 0 := vp_eq_zero q Dg hq2 hDgpos hqDg
  have hvAg1 : 1 ≤ vp q Ag := one_le_vp q Ag hq2 hAgpos hqAg
  rw [hvα, hvd, hvDg0, Nat.add_zero]
  exact Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le Nat.zero_lt_one hvAg1)

end E213.Lib.Math.NumberTheory.ModArith.ValuationAlg
