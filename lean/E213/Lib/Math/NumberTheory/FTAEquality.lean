import E213.Lib.Math.NumberTheory.FTAUniqueness
import E213.Lib.Math.NumberTheory.GaussTotient

/-!
# Valuation under division by a prime — the infrastructure for FTA equality (∅-axiom)

Toward "a positive number is determined by its prime valuations" (`eq_of_vp_eq`, the converse
of `FTAUniqueness`, the tool a product identity like `N! = Π lcm(1..⌊N/i⌋)` needs): the hard,
genuinely-missing piece is **how `vp` behaves under division by a prime factor**. That is
supplied here, ∅-axiom, from `vp_mul` + `vp_prime_single`:

  * `div_pos_of_dvd` — `p ∣ b`, `0 < b ⟹ 0 < b/p`;
  * `vp_div_self`  — `vp p b = vp p (b/p) + 1`  (the divided prime's valuation drops by one);
  * `vp_div_other` — `vp q b = vp q (b/p)`       (other primes' valuations are unchanged).

These make the FTA-equality induction (`prodL L ∣ b` from `countOcc q L ≤ vp q b`, peeling a
prime and dividing `b`) elementary; the assembly + `eq_of_vp_eq` is the next step (see HANDOFF
— the cited lemmas are all PURE; the remaining work is a propext-free assembly).
-/

namespace E213.Lib.Math.NumberTheory.FTAEquality

open E213.Lib.Math.NumberTheory.FTAUniqueness (vp_prime_single)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul)
open E213.Meta.Nat.Valuation (vp)
open E213.Lib.Math.NumberTheory.GaussTotient (mul_div_of_dvd)

/-- The cofactor `b/p` is positive when `p ∣ b`, `0 < b`. -/
theorem div_pos_of_dvd {p b : Nat} (hpb : p ∣ b) (hb : 0 < b) : 0 < b / p := by
  rcases Nat.eq_zero_or_pos (b / p) with h0 | hpos
  · exfalso
    have hcof : p * (b / p) = b := mul_div_of_dvd hpb
    rw [h0, Nat.mul_zero] at hcof
    exact Nat.lt_irrefl 0 (hcof ▸ hb)
  · exact hpos

/-- ★★ **`vp` of the divided prime drops by one**: `vp p b = vp p (b/p) + 1` for a prime
    `p ∣ b`.  From `vp_mul` on `b = p·(b/p)` and `vp p p = 1`. -/
theorem vp_div_self {p b : Nat} (hp : IsPrime213 p) (hpb : p ∣ b) (hb : 0 < b) :
    vp p b = vp p (b / p) + 1 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hbp : 0 < b / p := div_pos_of_dvd hpb hb
  have hcof : p * (b / p) = b := mul_div_of_dvd hpb
  have hmul : vp p (p * (b / p)) = vp p p + vp p (b / p) := vp_mul hp hppos hbp
  have hpp : vp p p = 1 := by rw [vp_prime_single hp hp]; rw [if_pos rfl]
  rw [hcof] at hmul
  rw [hmul, hpp, Nat.add_comm]

/-- ★★ **`vp` of other primes is unchanged**: `vp q b = vp q (b/p)` for distinct primes
    `q ≠ p`, `p ∣ b`.  From `vp_mul` on `b = p·(b/p)` and `vp q p = 0`. -/
theorem vp_div_other {p q b : Nat} (hp : IsPrime213 p) (hq : IsPrime213 q)
    (hqp : q ≠ p) (hpb : p ∣ b) (hb : 0 < b) : vp q b = vp q (b / p) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hbp : 0 < b / p := div_pos_of_dvd hpb hb
  have hcof : p * (b / p) = b := mul_div_of_dvd hpb
  have hmul : vp q (p * (b / p)) = vp q p + vp q (b / p) := vp_mul hq hppos hbp
  have hqp0 : vp q p = 0 := by
    rw [vp_prime_single hq hp, if_neg (fun e => hqp e.symm)]
  rw [hcof] at hmul
  rw [hmul, hqp0, Nat.zero_add]

end E213.Lib.Math.NumberTheory.FTAEquality
