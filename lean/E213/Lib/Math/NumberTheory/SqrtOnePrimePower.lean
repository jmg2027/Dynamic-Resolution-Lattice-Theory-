import E213.Lib.Math.NumberTheory.WilsonValue
import E213.Lib.Math.NumberTheory.PrimesThreeModFour

/-!
# Scratch: Wilson `±1` classification — the `n = pᵏ` (odd prime power) case

`sqrt_one_prime_power` : over ℤ/pᵏ (odd prime `p`), the only square roots of `1`
are `1` and `pᵏ − 1`.  Then `wilson_neg_one_prime_power` follows from
`WilsonValue.wilson_neg_one_of_sqrt_trivial`.
-/

namespace E213.Lib.Math.NumberTheory.SqrtOnePrimePower

open E213.Meta.Nat.VpMul (IsPrime213 euclid_lemma vp_mul vp_self_pow)
open E213.Meta.Nat.Valuation (vp pow_vp_dvd vp_not_dvd_succ le_vp_iff)
open E213.Meta.Nat.Gcd213 (dvd_sub_213)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub)
open E213.Tactic.NatHelper (add_sub_cancel_right sub_add_cancel)

/-! ## §1 — the keystone -/

/-- ★ **Square roots of `1` over ℤ/pᵏ (odd prime power) are trivial.**
    For odd prime `p`, `k ≥ 1`, a unit `0 < x < pᵏ` with `x² ≡ 1 (mod pᵏ)`
    is `1` or `pᵏ − 1`. -/
theorem sqrt_one_prime_power (p k x : Nat) (hp : IsPrime213 p) (hodd : p % 2 = 1)
    (hk : 0 < k) (hx : x < p ^ k) (hx0 : 0 < x)
    (hsq : (x * x) % (p ^ k) = 1 % (p ^ k)) : x = 1 ∨ x = p ^ k - 1 := by
  have hp2 : 2 ≤ p := hp.1
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hpkpos : 0 < p ^ k := Nat.pos_pow_of_pos k hppos
  -- `p` is odd ⟹ `¬ p ∣ 2`
  have hp_not_dvd_2 : ¬ p ∣ 2 := by
    intro hd
    have hle : p ≤ 2 := le_of_dvd_pos p 2 (by decide) hd
    have hpe : p = 2 := Nat.le_antisymm hle hp2
    rw [hpe] at hodd
    exact absurd hodd (by decide)
  -- write `x = y + 1`
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, (sub_add_cancel hx0).symm⟩
  -- decide whether `y = 0` (i.e. `x = 1`)
  cases y with
  | zero => exact Or.inl rfl
  | succ z =>
    right
    -- now `x = z + 2`, so `x - 1 = z + 1 > 0`, `x + 1 = z + 3`
    -- `p^k ∣ x*x - 1`
    have hxx_ge : 1 ≤ (z + 1 + 1) * (z + 1 + 1) := by
      have : 0 < (z + 1 + 1) * (z + 1 + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      exact this
    have hdvd_xx : p ^ k ∣ ((z + 1 + 1) * (z + 1 + 1) - 1) :=
      mod_eq_dvd_sub _ 1 (p ^ k) hpkpos hxx_ge hsq
    -- `x*x - 1 = (x-1)*(x+1) = (z+1)*(z+3)`
    have hfactor : (z + 1 + 1) * (z + 1 + 1) - 1 = (z + 1) * (z + 3) := by
      have hid : (z + 1 + 1) * (z + 1 + 1) = (z + 1) * (z + 3) + 1 := by ring_nat
      rw [hid, add_sub_cancel_right]
    rw [hfactor] at hdvd_xx
    -- `vp p ((z+1)*(z+3)) ≥ k`
    have hz1pos : 0 < z + 1 := Nat.succ_pos z
    have hz3pos : 0 < z + 3 := Nat.succ_pos _
    have hprodpos : 0 < (z + 1) * (z + 3) := Nat.mul_pos hz1pos hz3pos
    have hvp_ge : k ≤ vp p ((z + 1) * (z + 3)) :=
      (le_vp_iff p ((z + 1) * (z + 3)) k hp2 hprodpos).mp hdvd_xx
    rw [vp_mul hp hz1pos hz3pos] at hvp_ge
    -- one of `vp p (z+1)`, `vp p (z+3)` is `0` (else `p ∣ 2`)
    -- prove `¬ (1 ≤ vp p (z+1) ∧ 1 ≤ vp p (z+3))`
    have hnot_both : ¬ (1 ≤ vp p (z + 1) ∧ 1 ≤ vp p (z + 3)) := by
      intro ⟨h1, h3⟩
      have hd1 : p ∣ (z + 1) := by
        have := (le_vp_iff p (z + 1) 1 hp2 hz1pos).mpr h1
        rwa [Nat.pow_one] at this
      have hd3 : p ∣ (z + 3) := by
        have := (le_vp_iff p (z + 3) 1 hp2 hz3pos).mpr h3
        rwa [Nat.pow_one] at this
      -- `p ∣ (z+3) - (z+1) = 2`
      have hle13 : z + 1 ≤ z + 3 := by
        exact Nat.add_le_add_left (by decide) z
      have hd2 : p ∣ ((z + 3) - (z + 1)) := dvd_sub_213 (z + 1) (z + 3) p hle13 hd1 hd3
      have hsub2 : (z + 3) - (z + 1) = 2 := by
        have : z + 3 = (z + 1) + 2 := by ring_nat
        rw [this, Nat.add_comm (z + 1) 2, add_sub_cancel_right]
      rw [hsub2] at hd2
      exact hp_not_dvd_2 hd2
    -- so `vp p (z+1) = 0 ∨ vp p (z+3) = 0`
    have hcase : vp p (z + 1) = 0 ∨ vp p (z + 3) = 0 := by
      by_cases ha : vp p (z + 1) = 0
      · exact Or.inl ha
      · right
        by_cases hb : vp p (z + 3) = 0
        · exact hb
        · exact absurd ⟨Nat.pos_of_ne_zero ha, Nat.pos_of_ne_zero hb⟩ hnot_both
    rcases hcase with ha | hb
    · -- `vp p (z+1) = 0` ⟹ `k ≤ vp p (z+3)` ⟹ `p^k ∣ (z+3)` ⟹ `z+3 = p^k`
      rw [ha, Nat.zero_add] at hvp_ge
      have hdvd3 : p ^ k ∣ (z + 3) := (le_vp_iff p (z + 3) k hp2 hz3pos).mpr hvp_ge
      have hge : p ^ k ≤ z + 3 := le_of_dvd_pos (p ^ k) (z + 3) hz3pos hdvd3
      -- but `x = z + 2 < p^k`, so `z + 3 ≤ p^k`; with `≥`, `z + 3 = p^k`
      have hlt : z + 1 + 1 < p ^ k := hx
      have hle3 : z + 3 ≤ p ^ k := by
        have : z + 1 + 1 + 1 ≤ p ^ k := Nat.succ_le_of_lt hlt
        have heq : z + 1 + 1 + 1 = z + 3 := by ring_nat
        rwa [heq] at this
      have heq3 : z + 3 = p ^ k := Nat.le_antisymm hle3 hge
      -- `x = z + 2 = p^k - 1`
      show z + 1 + 1 = p ^ k - 1
      rw [← heq3]
      show z + 1 + 1 = z + 3 - 1
      have : z + 3 = (z + 2) + 1 := by ring_nat
      rw [this, add_sub_cancel_right]
    · -- `vp p (z+3) = 0` ⟹ `k ≤ vp p (z+1)` ⟹ `p^k ∣ (z+1)`, but `z+1 < p^k` and `z+1 > 0`
      rw [hb, Nat.add_zero] at hvp_ge
      have hdvd1 : p ^ k ∣ (z + 1) := (le_vp_iff p (z + 1) k hp2 hz1pos).mpr hvp_ge
      have hge1 : p ^ k ≤ z + 1 := le_of_dvd_pos (p ^ k) (z + 1) hz1pos hdvd1
      -- but `z + 1 < z + 1 + 1 = x < p^k`
      have hlt1 : z + 1 < p ^ k :=
        Nat.lt_trans (Nat.lt_succ_self (z + 1)) hx
      exact absurd hge1 (Nat.not_le.mpr hlt1)

/-! ## §2 — the Wilson `−1` value corollary -/

open E213.Lib.Math.NumberTheory.WilsonValue (wilson_neg_one_of_sqrt_trivial)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem (prodMod)

/-- ★ **Wilson `−1` for an odd prime power.**  For odd prime `p`, `k ≥ 1`,
    `2 < pᵏ`, `∏(units of ℤ/pᵏ) ≡ pᵏ − 1 ≡ −1 (mod pᵏ)`. -/
theorem wilson_neg_one_prime_power (p k : Nat) (hp : IsPrime213 p) (hodd : p % 2 = 1)
    (hk : 0 < k) (hbig : 2 < p ^ k) :
    prodMod (p ^ k) (totativeList (p ^ k)) % (p ^ k) = (p ^ k - 1) % (p ^ k) :=
  wilson_neg_one_of_sqrt_trivial (p ^ k) hbig
    (fun u hu hu0 hsq => sqrt_one_prime_power p k u hp hodd hk hu hu0 hsq)

/-! ## §3 — smokes -/

/-- `IsPrime213 3`, ∅-axiom (`minFac 3 = 3` reduces, then `minFac_isPrime`). -/
theorem isPrime213_3 : IsPrime213 3 := by
  have h := E213.Lib.Math.NumberTheory.PrimesThreeModFour.minFac_isPrime
    (n := 3) (by decide)
  have he : E213.Lib.Math.NumberTheory.PrimeFactorization.minFac 3 = 3 := by decide
  rwa [he] at h

/-- `p = 3, k = 2` (n = 9): the only square roots of `1` are `{1, 8}`. -/
theorem smoke_sqrt_9 :
    (3 % 2 = 1) ∧
    (∀ x, x < 9 → 0 < x → (x * x) % 9 = 1 % 9 → x = 1 ∨ x = 8) := by
  refine ⟨by decide, ?_⟩
  decide

/-- `p = 5, k = 1` (n = 5): square roots of `1` are `{1, 4}`. -/
theorem smoke_sqrt_5 :
    (∀ x, x < 5 → 0 < x → (x * x) % 5 = 1 % 5 → x = 1 ∨ x = 4) := by
  decide

/-- `wilson_neg_one_prime_power` instance at n = 9: `∏ units ≡ 8`. -/
theorem smoke_wilson_9 :
    prodMod 9 (totativeList 9) % 9 = (9 - 1) % 9 ∧
    prodMod 9 (totativeList 9) = 8 := by
  refine ⟨by decide, by decide⟩

/-- `wilson_neg_one_prime_power` instance at n = 27: `∏ units ≡ 26`. -/
theorem smoke_wilson_27 :
    prodMod 27 (totativeList 27) % 27 = (27 - 1) % 27 := by
  decide

end E213.Lib.Math.NumberTheory.SqrtOnePrimePower
