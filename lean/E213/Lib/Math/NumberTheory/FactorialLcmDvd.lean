import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
import E213.Lib.Math.NumberTheory.FTALite

/-!
# FactorialLcmDvd — `k ∣ n!`, `lcm(1..n) ∣ n!`, and `2·lcm³ ∣ (n!)³`, ∅-axiom

The factorial-clearing inputs for the ζ(3) reduced presentation (the
recurrence-divisibility route to `zeta3HolonomicReal`): every `k ≤ n` divides
`n!`, hence `lcm(1..n) ∣ n!`; and for `n ≥ 4` the common factor
`c n = (n!)³/(2·lcm³)` is an integer (`2·lcm³ ∣ (n!)³`).  The extra factor `2`
comes from `2·2^L ∣ n!` where `2^L = 2^{v₂(lcm)}` and `2` are *distinct* factors
`≤ n` (`mul_dvd_factorial`), giving `v₂(n!) ≥ v₂(lcm)+1`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FactorialLcmDvd

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ factorial_pos)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (lcmUpTo lcmUpTo_dvd lcmUpTo_pos
  vp_lcmUpTo lcmExpCount_eq_floorLog floorLog floorLog_pow_le floorLog_ge)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul vp_monotone)
open E213.Lib.Math.NumberTheory.FTALite (dvd_of_forall_prime_vp_le)
open E213.Meta.Nat.Valuation (vp le_vp_iff vp_lt)

/-- Every positive `k ≤ n` divides `n!` (subtraction-free; `Nat.dvd_trans` carries
    propext, so the `k ≤ n` step composes the two dvd witnesses by hand). -/
theorem dvd_factorial {k : Nat} (hk : 0 < k) : ∀ {n : Nat}, k ≤ n → k ∣ factorial n := by
  intro n
  induction n with
  | zero => intro hkn; exact absurd (Nat.lt_of_lt_of_le hk hkn) (Nat.lt_irrefl 0)
  | succ n ih =>
    intro hkn
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · rcases ih (Nat.le_of_lt_succ hlt) with ⟨c, hc⟩
      exact ⟨(n + 1) * c, by rw [factorial_succ, hc]; ring_nat⟩
    · have heq : k = n + 1 := Nat.le_antisymm hkn hge
      exact ⟨factorial n, by rw [heq, factorial_succ]⟩

/-- `lcm(1..n) ∣ n!` — `n!` is a common multiple of `1..n`, so the least common
    multiple divides it (`lcmUpTo`'s universal property). -/
theorem lcmUpTo_dvd_factorial (n : Nat) : lcmUpTo n ∣ factorial n :=
  lcmUpTo_dvd (fun _ hk hkn => dvd_factorial hk hkn)

/-- Two *distinct* positive factors `a < b ≤ n` multiply to a divisor of `n!`
    (they sit at different indices in the product). -/
theorem mul_dvd_factorial {a b : Nat} (ha : 0 < a) (hab : a < b) :
    ∀ {n : Nat}, b ≤ n → a * b ∣ factorial n := by
  intro n
  induction n with
  | zero =>
    intro hbn
    have hb0 : 0 < b := Nat.lt_trans ha hab
    exact absurd (Nat.lt_of_lt_of_le hb0 hbn) (Nat.lt_irrefl 0)
  | succ n ih =>
    intro hbn
    rcases Nat.lt_or_ge b (n + 1) with hlt | hge
    · rcases ih (Nat.le_of_lt_succ hlt) with ⟨c, hc⟩
      exact ⟨(n + 1) * c, by rw [factorial_succ, hc]; ring_nat⟩
    · have heq : b = n + 1 := Nat.le_antisymm hbn hge
      rcases dvd_factorial ha (Nat.le_of_lt_succ (heq ▸ hab)) with ⟨c, hc⟩
      exact ⟨c, by rw [factorial_succ, heq, hc]; ring_nat⟩

/-- `m ∣ n → 0 < n → m ≤ n`, ∅-axiom (`Nat.le_of_dvd` carries propext). -/
theorem le_of_dvd_pos {m n : Nat} (hn : 0 < n) (h : m ∣ n) : m ≤ n := by
  rcases h with ⟨c, hc⟩
  rcases Nat.eq_zero_or_pos c with hc0 | hc1
  · subst hc0; rw [Nat.mul_zero] at hc; exact absurd (hc ▸ hn) (Nat.lt_irrefl 0)
  · calc m = m * 1 := (Nat.mul_one m).symm
      _ ≤ m * c := Nat.mul_le_mul_left m hc1
      _ = n := hc.symm

/-- `Prime213 2`: `2` is prime (a divisor `d ∣ 2` is `≤ 2` and nonzero, so `1` or `2`). -/
theorem prime2 : Prime213 2 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hd2 : d ≤ 2 := le_of_dvd_pos (by decide) hd
  rcases Nat.lt_or_ge d 1 with h0 | h1
  · have hd0 : d = 0 := Nat.le_antisymm (Nat.le_of_lt_succ h0) (Nat.zero_le d)
    subst hd0
    rcases hd with ⟨c, hc⟩
    rw [Nat.zero_mul] at hc
    exact absurd hc (by decide)
  · rcases Nat.lt_or_ge d 2 with h1' | h2
    · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h1') h1)
    · exact Or.inr (Nat.le_antisymm hd2 h2)

/-- `x³ = x·x·x`. -/
private theorem cube (x : Nat) : x ^ 3 = x * x * x := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]

/-- `vₚ(x³) = 3·vₚ(x)` at a prime, `x > 0`. -/
theorem vp_pow3 {q x : Nat} (hq : Prime213 q) (hx : 0 < x) : vp q (x ^ 3) = 3 * vp q x := by
  have hxx : 0 < x * x := Nat.mul_pos hx hx
  rw [cube x, vp_mul hq hxx hx, vp_mul hq hx hx]
  ring_nat

/-- `vₚ(2) = 0` for an odd prime `q ≠ 2`. -/
theorem vp_two_eq_zero {q : Nat} (hq : Prime213 q) (hq2 : q ≠ 2) : vp q 2 = 0 := by
  rcases Nat.eq_zero_or_pos (vp q 2) with h | h
  · exact h
  · have hq1 : q ^ 1 ∣ 2 := (le_vp_iff q 2 1 hq.1 (by decide)).mpr h
    rw [Nat.pow_one] at hq1
    have hqle : q ≤ 2 := le_of_dvd_pos (by decide) hq1
    have hq3 : 2 < q := Nat.lt_of_le_of_ne hq.1 (Ne.symm hq2)
    exact absurd (Nat.lt_of_lt_of_le hq3 hqle) (Nat.lt_irrefl 2)

/-- `v₂(2) = 1`. -/
theorem vp_two_two : vp 2 2 = 1 := by
  have hge : 1 ≤ vp 2 2 := (le_vp_iff 2 2 1 (by decide) (by decide)).mp
    ⟨1, by rw [Nat.pow_one, Nat.mul_one]⟩
  have hlt : vp 2 2 < 2 := vp_lt 2 2 (by decide) (by decide)
  exact Nat.le_antisymm (Nat.le_of_lt_succ hlt) hge

/-- `v₂(lcm(1..n)) = ⌊log₂ n⌋` (`n ≥ 1`). -/
theorem vp_two_lcmUpTo {n : Nat} (hn : 1 ≤ n) : vp 2 (lcmUpTo n) = floorLog 2 n := by
  rw [vp_lcmUpTo prime2 n, lcmExpCount_eq_floorLog (by decide) hn]

/-- ★★ `v₂(n!) ≥ v₂(lcm(1..n)) + 1` for `n ≥ 4`: the distinct factors `2` and
    `2^{⌊log₂n⌋}` (both `≤ n`, both even, distinct since `⌊log₂n⌋ ≥ 2`) give
    `2^{⌊log₂n⌋+1} ∣ n!`. -/
theorem v2_fact_gt_lcm {n : Nat} (hn : 4 ≤ n) :
    vp 2 (lcmUpTo n) + 1 ≤ vp 2 (factorial n) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn
  have hL2 : 2 ≤ floorLog 2 n := floorLog_ge (by decide) (show (2:Nat) ^ 2 ≤ n from by
    rw [show (2:Nat) ^ 2 = 4 from by decide]; exact hn)
  have hpowle : (2:Nat) ^ floorLog 2 n ≤ n := floorLog_pow_le hn1
  have h2lt : (2:Nat) < 2 ^ floorLog 2 n :=
    Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hL2)
  -- 2 · 2^L = 2^{L+1} ∣ n!
  have hdvd : (2:Nat) ^ (floorLog 2 n + 1) ∣ factorial n := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact mul_dvd_factorial (by decide) h2lt hpowle
  have hvp : floorLog 2 n + 1 ≤ vp 2 (factorial n) :=
    (le_vp_iff 2 (factorial n) (floorLog 2 n + 1) (by decide) (factorial_pos n)).mp hdvd
  rw [vp_two_lcmUpTo hn1]
  exact hvp

/-- ★★★ **`2·lcm(1..n)³ ∣ (n!)³`** for `n ≥ 4` — the common factor
    `c n = (n!)³/(2·lcm³)` of the Apéry convergents is an integer.  Per prime:
    odd `q` by `lcm ∣ n!`; `q = 2` by `v₂(n!) ≥ v₂(lcm)+1` (`v2_fact_gt_lcm`). -/
theorem two_lcmCube_dvd_factCube {n : Nat} (hn : 4 ≤ n) :
    2 * lcmUpTo n ^ 3 ∣ factorial n ^ 3 := by
  have hlcm_pos := lcmUpTo_pos n
  have hfact_pos := factorial_pos n
  have hlcm3_pos : 0 < lcmUpTo n ^ 3 := Nat.pos_pow_of_pos 3 hlcm_pos
  refine dvd_of_forall_prime_vp_le (Nat.mul_pos (by decide) hlcm3_pos)
    (Nat.pos_pow_of_pos 3 hfact_pos) (fun q hq => ?_)
  rw [vp_mul hq (by decide) hlcm3_pos, vp_pow3 hq hlcm_pos, vp_pow3 hq hfact_pos]
  -- goal: vp q 2 + 3 * vp q (lcmUpTo n) ≤ 3 * vp q (factorial n)
  have hmono : vp q (lcmUpTo n) ≤ vp q (factorial n) :=
    vp_monotone hq hfact_pos (lcmUpTo_dvd_factorial n)
  by_cases hq2 : q = 2
  · subst hq2
    rw [vp_two_two]
    calc 1 + 3 * vp 2 (lcmUpTo n)
        ≤ 3 + 3 * vp 2 (lcmUpTo n) := Nat.add_le_add_right (by decide) _
      _ = 3 * (vp 2 (lcmUpTo n) + 1) := by ring_nat
      _ ≤ 3 * vp 2 (factorial n) := Nat.mul_le_mul_left 3 (v2_fact_gt_lcm hn)
  · rw [vp_two_eq_zero hq hq2, Nat.zero_add]
    exact Nat.mul_le_mul_left 3 hmono

end E213.Lib.Math.NumberTheory.FactorialLcmDvd
