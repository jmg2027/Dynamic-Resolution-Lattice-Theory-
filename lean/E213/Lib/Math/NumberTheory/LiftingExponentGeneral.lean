import E213.Lib.Math.NumberTheory.LiftingExponentMain
import E213.Lib.Math.NumberTheory.LiftingExponentCoprime

/-!
# Lifting-the-exponent, the general theorem `v_p(aⁿ − bⁿ) = v_p(a−b) + v_p(n)` (∅-axiom)

Assembles the two halves:
  * `LiftingExponentMain.lifting_prime_power` : `v_p(aᵖ − bᵖ) = v_p(a−b) + 1`  (prime exponent);
  * `LiftingExponentCoprime.lifting_coprime` : `v_p(aᵐ − bᵐ) = v_p(a−b)`  (`p ∤ m`).

**Step A** (`vp_pow_pk`): iterate the prime-power kernel `k` times to get
`v_p(a^{pᵏ} − b^{pᵏ}) = v_p(a−b) + k`.  **Step B**: factor `n = pᵏ·m` with `k = v_p(n)`, `p ∤ m`;
then `aⁿ − bⁿ = (a^{pᵏ})^m − (b^{pᵏ})^m`, and the coprime case gives `v_p = v_p(a^{pᵏ} − b^{pᵏ})
= v_p(a−b) + k = v_p(a−b) + v_p(n)`.  For an odd prime `p` (`3 ≤ p`), `p ∣ (a−b)`, `p ∤ b`, `b < a`,
`n ≥ 1`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.LiftingExponentGeneral

open E213.Lib.Math.NumberTheory.LiftingExponentMain (lifting_prime_power)
open E213.Lib.Math.NumberTheory.LiftingExponentCoprime (lifting_coprime)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.Valuation (vp pow_vp_dvd vp_not_dvd_succ le_vp_iff)
open E213.Meta.Nat.VpMul (vp_pow vp_self_pow IsPrime213)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)
open E213.Meta.Nat.PowBasic (powBase_lt pow_mul_pure)
open E213.Meta.Nat.NatRing213 (nat_add_sub_self_right)

/-- Pure `0 < a − b` from `b < a` (core `sub_pos_pure` leaks `propext`). -/
theorem sub_pos_pure {a b : Nat} (h : b < a) : 0 < a - b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  have hab : a - b = 1 + k := by
    rw [← hk, show b + 1 + k = (1 + k) + b from by ring_nat]
    exact nat_add_sub_self_right (1 + k) b
  rw [hab]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 1 k)

/-- `p ∤ b → p ∤ bᵉ` for prime `p` (`b > 0`), via `v_p(bᵉ) = e·v_p(b) = 0`. -/
theorem not_dvd_pow {p b : Nat} (hp : IsPrime213 p) (hpb : ¬ p ∣ b) (hb : 0 < b) (e : Nat) :
    ¬ p ∣ b ^ e := by
  intro h
  have hbe : 0 < b ^ e := Nat.pos_pow_of_pos e hb
  have h1 : 1 ≤ vp p (b ^ e) := (le_vp_iff p (b ^ e) 1 hp.1 hbe).mp (by rwa [Nat.pow_one])
  rw [vp_pow hp hb e, vp_eq_zero_of_not_dvd hp hb hpb, Nat.mul_zero] at h1
  exact absurd h1 (by decide)

/-- `p ∣ (a−b) → 1 ≤ v_p(a−b)` (`a−b > 0`). -/
theorem one_le_vp_of_dvd {p x : Nat} (hp : Prime213 p) (hx : 0 < x) (h : p ∣ x) :
    1 ≤ vp p x := (le_vp_iff p x 1 hp.1 hx).mp (by rwa [Nat.pow_one])

/-- ★★★★ **Step A**: `v_p(a^{pᵏ} − b^{pᵏ}) = v_p(a−b) + k` (iterate the prime-power kernel). -/
theorem vp_pow_pk (a b p : Nat) (hp : Prime213 p) (hp3 : 3 ≤ p)
    (hba : b < a) (hpd : p ∣ (a - b)) (hpb : ¬ p ∣ b) :
    ∀ k, vp p (a ^ (p ^ k) - b ^ (p ^ k)) = vp p (a - b) + k := by
  have hpI : IsPrime213 p := ⟨hp.1, hp.2⟩
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hpb (h ▸ ⟨0, rfl⟩))
  intro k
  induction k with
  | zero =>
      show vp p (a ^ (p ^ 0) - b ^ (p ^ 0)) = vp p (a - b) + 0
      rw [Nat.pow_zero, Nat.pow_one, Nat.pow_one, Nat.add_zero]
  | succ k ih =>
      -- a^(p^(k+1)) = (a^(p^k))^p
      have hAB : b ^ (p ^ k) < a ^ (p ^ k) := powBase_lt hba (Nat.pos_pow_of_pos k hp0)
      have hApos : 0 < a ^ (p ^ k) - b ^ (p ^ k) := sub_pos_pure hAB
      have hpAB : p ∣ (a ^ (p ^ k) - b ^ (p ^ k)) := by
        have : 1 ≤ vp p (a ^ (p ^ k) - b ^ (p ^ k)) := by
          rw [ih]; exact Nat.le_trans (one_le_vp_of_dvd hp (sub_pos_pure hba) hpd) (Nat.le_add_right _ k)
        have := (le_vp_iff p (a ^ (p ^ k) - b ^ (p ^ k)) 1 hp.1 hApos).mpr this
        rwa [Nat.pow_one] at this
      have hpB : ¬ p ∣ b ^ (p ^ k) := not_dvd_pow hpI hpb hb (p ^ k)
      show vp p (a ^ (p ^ (k + 1)) - b ^ (p ^ (k + 1))) = vp p (a - b) + (k + 1)
      rw [Nat.pow_succ, pow_mul_pure a (p ^ k) p, pow_mul_pure b (p ^ k) p,
          lifting_prime_power (a ^ (p ^ k)) (b ^ (p ^ k)) p hp hp3 hAB hpAB hpB, ih,
          Nat.add_assoc]

/-- **Step B (abstract)**: with the exponent already factored as `pᵏ·m` (`p ∤ m`, `m ≥ 1`),
    `v_p(a^{pᵏ·m} − b^{pᵏ·m}) = v_p(a−b) + k`.  `k, m` are free here. -/
theorem lte_aux (a b p k m : Nat) (hp : Prime213 p) (hp3 : 3 ≤ p)
    (hba : b < a) (hpd : p ∣ (a - b)) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ m) (hm1 : 1 ≤ m) :
    vp p (a ^ (p ^ k * m) - b ^ (p ^ k * m)) = vp p (a - b) + k := by
  have hpI : IsPrime213 p := ⟨hp.1, hp.2⟩
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hpb (h ▸ ⟨0, rfl⟩))
  have hpk0 : 0 < p ^ k := Nat.pos_pow_of_pos k hp0
  have hAB : b ^ (p ^ k) < a ^ (p ^ k) := powBase_lt hba hpk0
  have hApos : 0 < a ^ (p ^ k) - b ^ (p ^ k) := sub_pos_pure hAB
  have hpAB : p ∣ (a ^ (p ^ k) - b ^ (p ^ k)) := by
    have h1 : 1 ≤ vp p (a ^ (p ^ k) - b ^ (p ^ k)) := by
      rw [vp_pow_pk a b p hp hp3 hba hpd hpb k]
      exact Nat.le_trans (one_le_vp_of_dvd hp (sub_pos_pure hba) hpd) (Nat.le_add_right _ _)
    have := (le_vp_iff p _ 1 hp.1 hApos).mpr h1
    rwa [Nat.pow_one] at this
  have hpB : ¬ p ∣ b ^ (p ^ k) := not_dvd_pow hpI hpb hb (p ^ k)
  rw [pow_mul_pure a (p ^ k) m, pow_mul_pure b (p ^ k) m,
      lifting_coprime (a ^ (p ^ k)) (b ^ (p ^ k)) m p hp hm1 hpm hAB hpAB hpB,
      vp_pow_pk a b p hp hp3 hba hpd hpb k]

/-- ★★★★★ **Lifting-the-exponent (general)**: for an odd prime `p` (`3 ≤ p`) with `p ∣ (a−b)`,
    `p ∤ b`, `b < a`, `n ≥ 1`,  `v_p(aⁿ − bⁿ) = v_p(a−b) + v_p(n)`. -/
theorem lte (a b p n : Nat) (hp : Prime213 p) (hp3 : 3 ≤ p)
    (hba : b < a) (hpd : p ∣ (a - b)) (hpb : ¬ p ∣ b) (hn : 1 ≤ n) :
    vp p (a ^ n - b ^ n) = vp p (a - b) + vp p n := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hn0 : 0 < n := hn
  obtain ⟨m, hm⟩ := pow_vp_dvd p n
  have hpkm0 : 0 < p ^ (vp p n) := Nat.pos_pow_of_pos (vp p n) hp0
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, Nat.mul_zero] at hm; exact absurd (hm ▸ hn0) (Nat.lt_irrefl 0)
    · exact hpos
  have hpm : ¬ p ∣ m := by
    intro ⟨m', hm'⟩
    have hdvd : p ^ (vp p n + 1) ∣ n :=
      ⟨m', hm.trans (by rw [hm', Nat.pow_succ]; ring_nat)⟩
    exact vp_not_dvd_succ p n hp.1 hn0 hdvd
  have hgoal : a ^ n - b ^ n = a ^ (p ^ (vp p n) * m) - b ^ (p ^ (vp p n) * m) := by rw [← hm]
  rw [hgoal, lte_aux a b p (vp p n) m hp hp3 hba hpd hpb hpm hm1]

end E213.Lib.Math.NumberTheory.LiftingExponentGeneral
