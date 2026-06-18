import E213.Lib.Math.NumberTheory.SqrtOnePrimePower
import E213.Lib.Math.NumberTheory.WilsonValue
import E213.Lib.Math.NumberTheory.ModArith.EulerConverse

/-!
# Scratch: Wilson `±1` classification — the `n = 2pᵏ` case (∅-axiom)
-/

namespace E213.Lib.Math.NumberTheory.SqrtOneTwoPrimePower

open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm
   mod_eq_dvd_sub dvd_sub_213 succ_sub_self_213)
open E213.Tactic.NatHelper (sub_add_cancel)
open E213.Meta.Nat.AddMod213
  (div_add_mod add_mod_gen mod_mod mod_two_zero_or_one dvd_of_mod_eq_zero)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.NatDiv213 (div_lt_of_lt_mul)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
  (coprime_of_coprime_mul_left dvd_trans_213 eq_one_of_dvd_one)
open E213.Lib.Math.NumberTheory.SqrtOnePrimePower (sqrt_one_prime_power)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (mod_eq_of_dvd_sub)
open E213.Lib.Math.NumberTheory.WilsonValue (wilson_neg_one_of_sqrt_trivial)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem (prodMod)

/-! ## helpers -/

/-- `p % 2 = 1 → p^k % 2 = 1`. -/
theorem pow_odd : ∀ (p k : Nat), p % 2 = 1 → (p ^ k) % 2 = 1
  | _, 0, _ => rfl
  | p, k+1, hp => by
    show (p ^ k * p) % 2 = 1
    rw [mul_mod_pure (p ^ k) p 2, pow_odd p k hp, hp]

/-- `p % 2 = 1 → ∃ t, p^k = 2*t + 1` (odd witness). -/
theorem pow_odd_witness (p k : Nat) (hp : p % 2 = 1) : ∃ t, p ^ k = 2 * t + 1 := by
  refine ⟨p ^ k / 2, ?_⟩
  have h := div_add_mod (p ^ k) 2
  rw [pow_odd p k hp] at h
  exact h.symm

/-! ## §1 — the keystone -/

/-- ★ **Square roots of `1` over ℤ/(2pᵏ) (odd prime power) are trivial.** -/
theorem sqrt_one_two_prime_power (p k x : Nat) (hp : IsPrime213 p) (hodd : p % 2 = 1)
    (hk : 0 < k) (hx : x < 2 * p ^ k) (hx0 : 0 < x)
    (hcop : gcd213 x (2 * p ^ k) = 1)
    (hsq : (x * x) % (2 * p ^ k) = 1 % (2 * p ^ k)) :
    x = 1 ∨ x = 2 * p ^ k - 1 := by
  have hp2 : 2 ≤ p := hp.1
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hpkpos : 0 < p ^ k := Nat.pos_pow_of_pos k hppos
  have hpk_odd : (p ^ k) % 2 = 1 := pow_odd p k hodd
  -- `p^k ≥ 3`: p ≥ 3 (odd prime), p^k ≥ p ≥ 3
  have hp3 : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with h | h
    · -- p < 3 and p ≥ 2, so p = 2, contradicting odd
      exfalso
      have hpe : p = 2 := Nat.le_antisymm (Nat.le_of_lt_succ h) hp2
      rw [hpe] at hodd; exact absurd hodd (by decide)
    · exact h
  -- `1 ≤ x*x`
  have hxxpos : 0 < x * x := Nat.mul_pos hx0 hx0
  have hxx1 : 1 ≤ x * x := hxxpos
  -- `2*p^k ∣ x*x - 1`
  have htwopk_pos : 0 < 2 * p ^ k := Nat.mul_pos (by decide) hpkpos
  have hdvd2pk : 2 * p ^ k ∣ (x * x - 1) :=
    mod_eq_dvd_sub (x * x) 1 (2 * p ^ k) htwopk_pos hxx1 hsq
  -- `p^k ∣ 2*p^k`, hence `p^k ∣ x*x - 1`
  have hpk_dvd_2pk : p ^ k ∣ 2 * p ^ k := ⟨2, Nat.mul_comm 2 (p ^ k)⟩
  have hdvdpk : p ^ k ∣ (x * x - 1) :=
    dvd_trans_213 hpk_dvd_2pk hdvd2pk
  -- residue `r = x % p^k`
  obtain ⟨r, hr_def⟩ : ∃ r, x % p ^ k = r := ⟨_, rfl⟩
  have hr_lt : r < p ^ k := hr_def ▸ Nat.mod_lt x hpkpos
  -- `(r*r) % p^k = 1 % p^k`
  have hxx_mod : (x * x) % (p ^ k) = 1 % (p ^ k) :=
    mod_eq_of_dvd_sub (p ^ k) (x * x) 1 hxx1 hdvdpk
  have hrr_mod : (r * r) % (p ^ k) = 1 % (p ^ k) := by
    have h := mul_mod_pure x x (p ^ k)
    rw [hr_def] at h
    rw [← h]; exact hxx_mod
  -- `0 < r` (else p^k ∣ x, contradicting coprimality)
  have hcop_pk : gcd213 x (p ^ k) = 1 := by
    have h2pk : (2 : Nat) * p ^ k = 2 * p ^ k := rfl
    -- gcd213 x (2 * p^k) = 1 → gcd213 x (p^k) = 1
    have := coprime_of_coprime_mul_left (a := x) (b := p ^ k) (c := 2)
    -- need gcd213 x (p^k * 2) = 1; rewrite 2*p^k = p^k*2
    apply this
    rw [Nat.mul_comm (p ^ k) 2]; exact hcop
  have hpk_ge3 : 3 ≤ p ^ k :=
    Nat.le_trans hp3 (Nat.le_trans (Nat.le_of_eq (Nat.pow_one p).symm)
      (Nat.pow_le_pow_right hppos hk))
  have hr_pos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrp
    · exfalso
      have hpk_dvd_x : p ^ k ∣ x := dvd_of_mod_eq_zero (hr_def.trans hr0)
      have hpk_dvd_g : p ^ k ∣ gcd213 x (p ^ k) :=
        gcd213_greatest x (p ^ k) (p ^ k) hpk_dvd_x ⟨1, (Nat.mul_one _).symm⟩
      rw [hcop_pk] at hpk_dvd_g
      have hle1 : p ^ k ≤ 1 := le_of_dvd_pos (p ^ k) 1 (by decide) hpk_dvd_g
      exact absurd (Nat.le_trans hpk_ge3 hle1) (by decide)
    · exact hrp
  -- apply the prime-power keystone to `r`
  have hr_triv : r = 1 ∨ r = p ^ k - 1 :=
    sqrt_one_prime_power p k r hp hodd hk hr_lt hr_pos hrr_mod
  -- the two lifts: x = r ∨ x = r + p^k, since x < 2*p^k and x = p^k*(x/p^k)+r
  obtain ⟨t, hpk_eq⟩ := pow_odd_witness p k hodd  -- p^k = 2*t+1
  have hdiv_lt : x / p ^ k < 2 := div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  have hdm : p ^ k * (x / p ^ k) + r = x := by
    have := div_add_mod x (p ^ k); rw [hr_def] at this; exact this
  have hq01 : x / p ^ k = 0 ∨ x / p ^ k = 1 := by
    match hq : x / p ^ k with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | q+2 =>
      exfalso
      rw [hq] at hdiv_lt
      exact absurd hdiv_lt (Nat.not_lt.mpr (Nat.le_add_left 2 q))
  have hlift : x = r ∨ x = r + p ^ k := by
    rcases hq01 with hq | hq
    · left
      rw [hq, Nat.mul_zero, Nat.zero_add] at hdm; exact hdm.symm
    · right
      rw [hq, Nat.mul_one] at hdm
      rw [← hdm, Nat.add_comm]
  -- parity: x % 2 = 1
  have hx_odd : x % 2 = 1 := by
    rcases mod_two_zero_or_one x with hx2 | hx2
    · exfalso
      have h2x : (2 : Nat) ∣ x := dvd_of_mod_eq_zero hx2
      have h2dvd2pk : (2 : Nat) ∣ 2 * p ^ k := ⟨p ^ k, rfl⟩
      have h2g : (2 : Nat) ∣ gcd213 x (2 * p ^ k) :=
        gcd213_greatest x (2 * p ^ k) 2 h2x h2dvd2pk
      rw [hcop] at h2g
      exact absurd (le_of_dvd_pos 2 1 (by decide) h2g) (by decide)
    · exact hx2
  -- select the lift by parity, using `r = 1 ∨ r = p^k - 1`
  rcases hr_triv with hr1 | hrpk
  · -- r = 1
    subst hr1
    rcases hlift with hl | hl
    · exact Or.inl hl
    · -- x = 1 + p^k = even, contradicting x odd
      exfalso
      rw [hpk_eq] at hl   -- x = 1 + (2*t+1)
      have : x % 2 = 0 := by
        rw [hl]
        -- (1 + (2*t+1)) % 2 = (2 + 2*t) % 2 = 0
        have he : 1 + (2 * t + 1) = 2 * (t + 1) := by ring_nat
        rw [he]
        exact E213.Tactic.NatHelper.mul_mod_right 2 (t + 1)
      rw [hx_odd] at this; exact absurd this (by decide)
  · -- r = p^k - 1
    rcases hlift with hl | hl
    · -- x = r = p^k - 1 = even (p^k odd), contradicting x odd
      exfalso
      rw [hrpk, hpk_eq] at hl  -- x = (2*t+1) - 1
      have hsub : (2 * t + 1) - 1 = 2 * t := add_sub_cancel_right (2 * t) 1
      rw [hsub] at hl
      have : x % 2 = 0 := by rw [hl]; exact E213.Tactic.NatHelper.mul_mod_right 2 t
      rw [hx_odd] at this; exact absurd this (by decide)
    · -- x = r + p^k = (p^k - 1) + p^k = 2*p^k - 1
      right
      rw [hl, hrpk]
      -- (p^k - 1) + p^k = 2*p^k - 1
      have hge1 : 1 ≤ p ^ k := hpkpos
      rw [hpk_eq]  -- ((2t+1) - 1) + (2t+1) = 2*(2t+1) - 1
      have hsub : (2 * t + 1) - 1 = 2 * t := add_sub_cancel_right (2 * t) 1
      rw [hsub]
      -- 2*t + (2*t+1) = 2*(2*t+1) - 1
      have : 2 * t + (2 * t + 1) = 2 * (2 * t + 1) - 1 := by
        have h2 : 2 * (2 * t + 1) = (2 * t + (2 * t + 1)) + 1 := by ring_nat
        rw [h2]; exact (add_sub_cancel_right (2 * t + (2 * t + 1)) 1).symm
      exact this

/-! ## §2 — coprimality is automatic for square roots of 1 -/

/-- A solution of `u² ≡ 1 (mod n)` is automatically a unit. -/
theorem sqrt_one_coprime (n u : Nat) (hn : 0 < n) (hu0 : 0 < u)
    (hsq : (u * u) % n = 1 % n) : gcd213 u n = 1 := by
  have huu1 : 1 ≤ u * u := Nat.mul_pos hu0 hu0
  have hdvd : n ∣ (u * u - 1) := mod_eq_dvd_sub (u * u) 1 n hn huu1 hsq
  have hg_n : gcd213 u n ∣ n := gcd213_dvd_right u n
  obtain ⟨c, hc⟩ := gcd213_dvd_left u n
  have hg_uu : gcd213 u n ∣ (u * u) :=
    ⟨c * u, by
      have h1 : gcd213 u n * (c * u) = (gcd213 u n * c) * u :=
        (E213.Tactic.NatHelper.mul_assoc (gcd213 u n) c u).symm
      rw [h1, ← hc]⟩
  have hg_uu1 : gcd213 u n ∣ (u * u - 1) := dvd_trans_213 hg_n hdvd
  -- abstract `w := u*u - 1`, with `hw : w + 1 = u*u`
  obtain ⟨w, hw⟩ : ∃ w, w + 1 = u * u ∧ w = u * u - 1 := ⟨u * u - 1, sub_add_cancel huu1, rfl⟩
  obtain ⟨hw1, hw2⟩ := hw
  have hsub_le' : w ≤ u * u := by rw [← hw1]; exact Nat.le_succ w
  have hg_uu1' : gcd213 u n ∣ w := hw2 ▸ hg_uu1
  have hg_diff : gcd213 u n ∣ (u * u - w) :=
    dvd_sub_213 w (u * u) (gcd213 u n) hsub_le' hg_uu1' hg_uu
  have hone : u * u - w = 1 := by
    rw [← hw1]; exact succ_sub_self_213 w
  rw [hone] at hg_diff
  exact eq_one_of_dvd_one hg_diff

/-! ## §3 — the Wilson `−1` corollary -/

/-- ★ **Wilson `−1` for `n = 2pᵏ`** (odd prime power doubled). -/
theorem wilson_neg_one_two_prime_power (p k : Nat) (hp : IsPrime213 p)
    (hodd : p % 2 = 1) (hk : 0 < k) (hbig : 2 < 2 * p ^ k) :
    prodMod (2 * p ^ k) (totativeList (2 * p ^ k)) % (2 * p ^ k)
      = (2 * p ^ k - 1) % (2 * p ^ k) := by
  have hn_pos : 0 < 2 * p ^ k := Nat.lt_trans (by decide) hbig
  refine wilson_neg_one_of_sqrt_trivial (2 * p ^ k) hbig (fun u hu hu0 hsq => ?_)
  have hcop : gcd213 u (2 * p ^ k) = 1 := sqrt_one_coprime (2 * p ^ k) u hn_pos hu0 hsq
  exact sqrt_one_two_prime_power p k u hp hodd hk hu hu0 hcop hsq

/-! ## §4 — small cases + smokes -/

/-- **n = 4**: units `{1,3}`, `∏ ≡ 3 ≡ −1 (mod 4)`. -/
theorem wilson_neg_one_four :
    prodMod 4 (totativeList 4) % 4 = 3 := by decide

/-- `sqrt_one_two_prime_power` smoke at `p=3,k=1` (n=6): √1 coprime are `{1,5}`. -/
theorem smoke_sqrt_6 :
    (∀ x, x < 6 → 0 < x → gcd213 x 6 = 1 → (x * x) % 6 = 1 % 6 → x = 1 ∨ x = 5) := by
  decide

/-- `wilson_neg_one_two_prime_power` smoke at n=6: `∏ units {1,5} ≡ 5 ≡ −1`. -/
theorem smoke_wilson_6 :
    prodMod 6 (totativeList 6) % 6 = (6 - 1) % 6 ∧
    prodMod 6 (totativeList 6) = 5 := by
  refine ⟨by decide, by decide⟩

/-- `wilson_neg_one_two_prime_power` smoke at n=10 (`2·5`):
    units `{1,3,7,9}`, √1 = `{1,9}`, `∏ units ≡ 9 ≡ −1`. -/
theorem smoke_wilson_10 :
    prodMod 10 (totativeList 10) % 10 = (10 - 1) % 10 ∧
    prodMod 10 (totativeList 10) = 9 := by
  refine ⟨by decide, by decide⟩

end E213.Lib.Math.NumberTheory.SqrtOneTwoPrimePower
