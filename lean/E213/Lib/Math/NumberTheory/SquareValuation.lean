import E213.Lib.Math.NumberTheory.SquareCharacterization
import E213.Lib.Math.NumberTheory.SigmaParityComplete
import E213.Lib.Math.NumberTheory.MobiusDivisorSum
import E213.Lib.Math.NumberTheory.MobiusMultiplicative
import E213.Meta.Nat.VpMul

/-!
# General square characterization — `IsSquare n ↔ every prime valuation is even`

Closes crux #2 of the σ-parity programme: the all-primes generalization of
`SquareCharacterization.isSquare_iff` (the 2-adic split).

★★★ `isSquare_iff_all_vp_even (hn : 0 < n) :
        IsSquare n ↔ (∀ p, Prime213 p → vp p n % 2 = 0)`.

Strong induction on `n`, smallest-prime-power split `n = p^k·m` (the
`sigma_odd_square_odd` shape).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.SquareValuation

open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul)
open E213.Lib.Math.NumberTheory.SquareCharacterization (IsSquare coprime_isSquare_mul)
open E213.Lib.Math.NumberTheory.SigmaParityComplete (isSquare_prime_pow_iff)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (exists_prime_pow_cofactor prime_ne_not_dvd_pow)
open E213.Lib.Math.NumberTheory.MobiusMultiplicative (not_dvd_both_of_coprime)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpMul (vp_self_pow)

/-- One inductive step (extracted for axiom-localisation). -/
theorem step (n : Nat)
    (ih : ∀ j, j < n → 0 < j →
      (IsSquare j ↔ (∀ q, Prime213 q → vp q j % 2 = 0)))
    (hn : 0 < n) :
    IsSquare n ↔ (∀ q, Prime213 q → vp q n % 2 = 0) := by
  rcases Nat.lt_or_ge 1 n with hgt | hle
  · -- n > 1
    obtain ⟨p, k, m, hp, hk1, hmpos, hmlt, hcop, hmeq⟩ := exists_prime_pow_cofactor hgt
    have hp2 : 2 ≤ p := hp.1
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
    have hpk_pos : 0 < p ^ k := Nat.pos_pow_of_pos k hppos
    -- p ∣ p^k (k ≥ 1)
    have hp_dvd_pk : p ∣ p ^ k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk1).symm⟩
      exact ⟨p ^ j, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    -- p ∤ m  (from gcd(p^k, m) = 1)
    have hp_not_m : ¬ p ∣ m := fun hpm => not_dvd_both_of_coprime hp hcop ⟨hp_dvd_pk, hpm⟩
    have hvp_p_m : vp p m = 0 :=
      E213.Lib.Math.NumberTheory.MobiusMultiplicative.vp_zero_of_not_dvd hp hmpos hp_not_m
    -- IH on m
    have hm_iff : IsSquare m ↔ (∀ q, Prime213 q → vp q m % 2 = 0) := ih m hmlt hmpos
    -- IsSquare (p^k·m) ↔ (k even ∧ ∀ q prime, vp q m even)
    have hsq_iff : IsSquare (p ^ k * m) ↔
        (k % 2 = 0 ∧ (∀ q, Prime213 q → vp q m % 2 = 0)) := by
      refine (coprime_isSquare_mul hcop).trans (Iff.intro ?_ ?_)
      · rintro ⟨ha, hb⟩
        exact ⟨(isSquare_prime_pow_iff hp k).mp ha, hm_iff.mp hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨(isSquare_prime_pow_iff hp k).mpr ha, hm_iff.mpr hb⟩
    -- RHS for n = p^k·m: ∀ q prime, vp q (p^k·m) even ↔ (k even ∧ ∀ q prime, vp q m even)
    have hall_iff : (∀ q, Prime213 q → vp q (p ^ k * m) % 2 = 0) ↔
        (k % 2 = 0 ∧ (∀ q, Prime213 q → vp q m % 2 = 0)) := by
      constructor
      · intro hAll
        refine ⟨?_, ?_⟩
        · -- q = p : vp p (p^k·m) = k + 0 = k
          have hsp := hAll p hp
          rw [vp_mul hp hpk_pos hmpos, vp_self_pow hp k, hvp_p_m, Nat.add_zero] at hsp
          exact hsp
        · intro q hq
          have hsq' := hAll q hq
          rw [vp_mul hq hpk_pos hmpos] at hsq'
          -- vp q (p^k·m) = vp q (p^k) + vp q m even; vp q (p^k) even ⟹ vp q m even
          by_cases hqp : q = p
          · subst hqp
            -- goal: vp p m % 2 = 0; and vp p m = 0
            rw [hvp_p_m]
          · have hz : vp q (p ^ k) = 0 :=
              E213.Lib.Math.NumberTheory.MobiusMultiplicative.vp_zero_of_not_dvd hq hpk_pos
                (prime_ne_not_dvd_pow hp hq hqp k)
            rw [hz, Nat.zero_add] at hsq'
            exact hsq'
      · rintro ⟨hk, hm⟩ q hq
        rw [vp_mul hq hpk_pos hmpos]
        -- vp q (p^k) + vp q m, both even (vp q (p^k) even by split)
        have hpk_even : vp q (p ^ k) % 2 = 0 := by
          by_cases hqp : q = p
          · subst hqp; rw [vp_self_pow hq k]; exact hk
          · rw [E213.Lib.Math.NumberTheory.MobiusMultiplicative.vp_zero_of_not_dvd hq hpk_pos
              (prime_ne_not_dvd_pow hp hq hqp k)]
        have hm_even : vp q m % 2 = 0 := hm q hq
        -- (a + b) % 2 = 0 from a%2=0, b%2=0
        rw [E213.Meta.Nat.AddMod213.add_mod (by decide) (vp q (p ^ k)) (vp q m),
          hpk_even, hm_even]
    -- combine, transport via hmeq
    have hfinal : IsSquare (p ^ k * m) ↔ (∀ q, Prime213 q → vp q (p ^ k * m) % 2 = 0) :=
      hsq_iff.trans hall_iff.symm
    exact hmeq ▸ hfinal
  · -- n ≤ 1, with 0 < n ⟹ n = 1
    have hn_eq : n = 1 := Nat.le_antisymm hle hn
    subst hn_eq
    apply iff_of_true
    · exact ⟨1, rfl⟩
    · intro q hq
      -- vp q 1 = 0
      have hz : vp q 1 = 0 := by
        rcases Nat.eq_zero_or_pos (vp q 1) with h0 | hpos
        · exact h0
        · exfalso
          have hq2 : 2 ≤ q := hq.1
          have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq2
          have hdvd : q ^ 1 ∣ (1 : Nat) :=
            E213.Meta.Nat.Valuation.dtrans
              (E213.Meta.Nat.Valuation.pow_dvd_of_le q hpos)
              (E213.Meta.Nat.Valuation.pow_vp_dvd q 1)
          rw [Nat.pow_one] at hdvd
          have hqle : q ≤ 1 := E213.Tactic.Pow213.le_of_dvd_pos q 1 (by decide) hdvd
          exact absurd (Nat.le_trans hq2 hqle) (by decide)
      rw [hz]

/-- ★★★ **General square characterization**: `n > 0` is a perfect square iff every
    prime valuation `vp p n` is even.  The all-primes generalization of the 2-adic
    `SquareCharacterization.isSquare_iff`. -/
theorem isSquare_iff_all_vp_even {n : Nat} (hn : 0 < n) :
    IsSquare n ↔ (∀ p, Prime213 p → vp p n % 2 = 0) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    refine step n (fun j hj hjpos => ih j hj hjpos) hn

end E213.Lib.Math.NumberTheory.SquareValuation
