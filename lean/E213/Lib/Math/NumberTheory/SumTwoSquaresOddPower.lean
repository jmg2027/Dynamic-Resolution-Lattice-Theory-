import E213.Lib.Math.NumberTheory.InertPrimeThreeMod4
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.NatRing213

/-!
# Odd-power obstruction for sums of two squares (∅-axiom) — scratch

`even_vp_three_mod4`: a sum of two squares has **even** `q`-adic valuation at
every prime `q ≡ 3 (mod 4)`.  Descent on the valuation via the inert-prime
lemma `inert_three_mod4` (`q ∣ a²+b² ⟹ q∣a ∧ q∣b`).  Completes the "only if"
direction of the two-square characterization.
-/

namespace E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower

open E213.Lib.Math.NumberTheory.InertPrimeThreeMod4 (inert_three_mod4)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_self_pow)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)
open E213.Lib.Math.NumberTheory.PerfectNumbers (prime_of_bounded)

/-- `n` is a sum of two `Nat` squares. -/
def isSumTwoSqNat (n : Nat) : Prop := ∃ a b : Nat, n = a * a + b * b

/-! ## §1 — the valuation step: `vp q (q²·m) = 2 + vp q m` -/

/-- `vp q (q*q * m) = 2 + vp q m` for prime `q`, `m > 0`. -/
theorem vp_qsq_mul {q : Nat} (hq : IsPrime213 q) {m : Nat} (hm : 0 < m) :
    vp q (q * q * m) = 2 + vp q m := by
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.two_le
  have hqq_pos : 0 < q * q := Nat.mul_pos hqpos hqpos
  -- vp q (q*q) = 2
  have hqq : vp q (q * q) = 2 := by
    have hsp := vp_self_pow hq 2
    have he : q ^ 2 = q * q := by rw [Nat.pow_succ, Nat.pow_one]
    rw [he] at hsp; exact hsp
  rw [vp_mul hq hqq_pos hm, hqq]

/-! ## §2 — base case: `q ∤ n ⟹ vp q n = 0` (even) -/

theorem vp_even_of_not_dvd {q n : Nat} (hq : IsPrime213 q) (hn : 0 < n)
    (h : ¬ q ∣ n) : ∃ k, vp q n = 2 * k :=
  ⟨0, by rw [vp_eq_zero_of_not_dvd hq hn h, Nat.mul_zero]⟩

/-! ## §3 — strict-`<` helper for the descent -/

/-- `m < q*q*m` for prime `q` and `m > 0` (since `q*q ≥ 4 > 1`). -/
theorem lt_qsq_mul {q : Nat} (hq : IsPrime213 q) {m : Nat} (hm : 0 < m) :
    m < q * q * m := by
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.two_le
  -- 1 < q*q  (q ≥ 2, so q*q ≥ 2*1 = 2 > 1)
  have hqq : 1 < q * q := by
    have h2q : 2 ≤ q * q :=
      Nat.le_trans hq.two_le (Nat.le_mul_of_pos_right q hqpos)
    exact Nat.lt_of_lt_of_le (by decide) h2q
  -- m = 1*m < (q*q)*m
  have h1m : 1 * m < q * q * m :=
    E213.Meta.Nat.NatRing213.nat_mul_lt_mul_right hm hqq
  rwa [Nat.one_mul] at h1m

/-! ## §4 — the odd-power obstruction: even valuation at `q ≡ 3 (mod 4)` -/

/-- ★★★★★ **Even valuation at `q ≡ 3 (mod 4)`.**  A positive sum of two squares
    has even `q`-adic valuation at every prime `q ≡ 3 (mod 4)`.  Strong induction
    on `n`: if `q ∤ n` the valuation is `0`; if `q ∣ n` then `inert_three_mod4`
    forces `q∣a, q∣b`, so `n = q²·n'` with `n' = a'²+b'²` a smaller sum of two
    squares, and `vp q n = 2 + vp q n'` is even by IH. -/
theorem even_vp_three_mod4 {q : Nat} (hq : IsPrime213 q) (hmod : q % 4 = 3) :
    ∀ n, 0 < n → isSumTwoSqNat n → ∃ k, vp q n = 2 * k := fun n =>
  Nat.strongRecOn n
    (motive := fun n => 0 < n → isSumTwoSqNat n → ∃ k, vp q n = 2 * k)
    (fun n ih hn hsq => by
      have hq2 : 2 ≤ q := hq.two_le
      have hq1 : 1 < q := Nat.lt_of_lt_of_le (by decide) hq2
      obtain ⟨a, b, hab⟩ := hsq
      -- split on q ∣ n via decidable `n % q = 0`
      have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq2
      by_cases hdvd : n % q = 0
      · -- q ∣ n: descend
        have hqn : q ∣ n := E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hdvd
        have hqab : q ∣ (a * a + b * b) := by rw [← hab]; exact hqn
        obtain ⟨ha, hb⟩ := inert_three_mod4 q a b hq1 hq.2 hmod hqab
        obtain ⟨s, hs⟩ := ha
        obtain ⟨t, ht⟩ := hb
        -- n = q*q*(s*s+t*t)
        have hn_eq : n = q * q * (s * s + t * t) := by
          rw [hab, hs, ht]; ring_nat
        -- n' = s*s+t*t > 0  (else n = 0)
        have hn'_pos : 0 < s * s + t * t := by
          rcases Nat.eq_zero_or_pos (s * s + t * t) with h0 | hp
          · exfalso
            apply Nat.lt_irrefl 0
            have : n = 0 := by rw [hn_eq, h0, Nat.mul_zero]
            rwa [this] at hn
          · exact hp
        -- n' < n
        have hlt : s * s + t * t < n := by
          rw [hn_eq]; exact lt_qsq_mul hq hn'_pos
        -- IH on n'
        have hsq' : isSumTwoSqNat (s * s + t * t) := ⟨s, t, rfl⟩
        obtain ⟨k', hk'⟩ := ih (s * s + t * t) hlt hn'_pos hsq'
        -- vp q n = 2 + vp q n' = 2 + 2k' = 2*(k'+1)
        refine ⟨k' + 1, ?_⟩
        rw [hn_eq, vp_qsq_mul hq hn'_pos, hk']
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm 2 (2 * k')]
      · -- q ∤ n: vp = 0
        have hnd : ¬ q ∣ n := fun hd =>
          hdvd (E213.Meta.Nat.Valuation.mod_zero_of_dvd hqpos hd)
        exact vp_even_of_not_dvd hq hn hnd)

/-! ## §5 — contrapositive corollary -/

/-- ★★★★ **Odd valuation forbids two-square representation.**  If `vp q n` is odd
    at a prime `q ≡ 3 (mod 4)`, then `n` is not a sum of two squares. -/
theorem not_isSumTwoSqNat_of_odd_vp {q n : Nat} (hq : IsPrime213 q) (hmod : q % 4 = 3)
    (hn : 0 < n) (hodd : ¬ ∃ k, vp q n = 2 * k) : ¬ isSumTwoSqNat n := fun hsq =>
  hodd (even_vp_three_mod4 hq hmod n hn hsq)

/-! ## §6 — small-prime instances + closed-numeral smokes -/

/-- `3` is prime (213-native minimal-divisor form); via `prime_of_bounded`
    (`Prime213` and `IsPrime213` are the same conjunction). -/
theorem isPrime3 : IsPrime213 3 :=
  let h := prime_of_bounded (q := 3) (by decide) (B := 2) (by decide) (by decide); ⟨h.1, h.2⟩
/-- `7` is prime. -/
theorem isPrime7 : IsPrime213 7 :=
  let h := prime_of_bounded (q := 7) (by decide) (B := 3) (by decide) (by decide); ⟨h.1, h.2⟩

/-- `1` is not twice anything: rules out `vp = 1` being even. -/
theorem one_not_two_mul : ¬ ∃ k, (1 : Nat) = 2 * k := by
  rintro ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with h0 | hp
  · rw [h0, Nat.mul_zero] at hk; exact absurd hk (by decide)
  · -- k ≥ 1 ⟹ 2*k ≥ 2 > 1
    have h2k : 2 ≤ 2 * k := by
      have := Nat.mul_le_mul_left 2 hp; rwa [Nat.mul_one] at this
    rw [← hk] at h2k; exact absurd h2k (by decide)

/-- `vp 3 3 = 1` (closed). -/
theorem vp_3_3 : vp 3 3 = 1 := by decide
/-- `vp 3 9 = 2` (closed). -/
theorem vp_3_9 : vp 3 9 = 2 := by decide
/-- `vp 3 45 = 2` (closed; `45 = 3²·5`). -/
theorem vp_3_45 : vp 3 45 = 2 := by decide
/-- `vp 3 21 = 1` (closed; `21 = 3·7`). -/
theorem vp_3_21 : vp 3 21 = 1 := by decide

/-- ★ **`3` is not a sum of two squares** (`vp 3 3 = 1` is odd). -/
theorem not_isSumTwoSqNat_three : ¬ isSumTwoSqNat 3 :=
  not_isSumTwoSqNat_of_odd_vp isPrime3 (by decide) (by decide)
    (fun h => one_not_two_mul (vp_3_3 ▸ h))

/-- ★ **`21 = 3·7` is not a sum of two squares** (`vp 3 21 = 1` is odd). -/
theorem not_isSumTwoSqNat_twentyone : ¬ isSumTwoSqNat 21 :=
  not_isSumTwoSqNat_of_odd_vp isPrime3 (by decide) (by decide)
    (fun h => one_not_two_mul (vp_3_21 ▸ h))

end E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower
