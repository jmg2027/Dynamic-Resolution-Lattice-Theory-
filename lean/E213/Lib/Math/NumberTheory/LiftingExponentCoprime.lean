import E213.Lib.Math.NumberTheory.LiftingExponentMain

/-!
# Lifting-the-exponent: the `p ∤ n` case in valuation form `v_p(aⁿ − bⁿ) = v_p(a−b)` (∅-axiom)

The "coprime exponent" half of LTE.  Same binomial decomposition as the prime-power kernel, but the
exponent `m` need not be prime: `(b+d)ᵐ − bᵐ = m·b^{m−1}·d + R`, where now the **middle** term has
`v_p = v_p(d)` (because `p ∤ m`, so `v_p(m)=0`) and every **tail** term still has `v_p ≥ v_p(d)+1`
(because `v_p(dᵏ) ≥ 2·v_p(d) ≥ v_p(d)+1` for `k ≥ 2`, using `p ∣ d` — no `p ∣ C(m,k)` needed).
Strict-minimum `vp_add_eq_min` pins `v_p(aᵐ − bᵐ) = v_p(d) = v_p(a−b)`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.LiftingExponentCoprime

open E213.Lib.Math.NumberTheory.LiftingExponentMain
  (lte_decomp pk_dvd_pow dvd_of_eq_nat dvd_mul_right_nat)
open E213.Lib.Math.NumberTheory.LiftingExponentPP (vp_add_eq_min le_vp_sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.Valuation (vp le_vp_iff pow_dvd_of_le dtrans)
open E213.Meta.Nat.VpMul (vp_pow IsPrime213)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)
open E213.Meta.Nat.NatRing213 (nat_add_sub_self_right nat_sub_add_cancel)

theorem dvd_mul_left_nat {y : Nat} (z : Nat) : y ∣ z * y := ⟨z, by ring_nat⟩

/-- Middle term valuation in the `p ∤ m` case: `v_p((m₀+1)·b^{m₀}·d) = v_p(d)`. -/
theorem middle_vp2 (b d m₀ p : Nat) (hpp : Prime213 p)
    (hpm : ¬ p ∣ (m₀ + 1)) (hpb : ¬ p ∣ b) (hd : 0 < d) :
    vp p ((m₀ + 1) * b ^ m₀ * d) = vp p d := by
  have hpI : IsPrime213 p := ⟨hpp.1, hpp.2⟩
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hpb (h ▸ ⟨0, rfl⟩))
  have hbp : 0 < b ^ m₀ := Nat.pos_pow_of_pos m₀ hb
  have hm0 : 0 < m₀ + 1 := Nat.succ_pos m₀
  have hpb0 : 0 < (m₀ + 1) * b ^ m₀ := Nat.mul_pos hm0 hbp
  have hvm : vp p (m₀ + 1) = 0 := vp_eq_zero_of_not_dvd hpI hm0 hpm
  have hvb : vp p b = 0 := vp_eq_zero_of_not_dvd hpI hb hpb
  rw [E213.Lib.Math.NumberTheory.PrimeValuation.vp_mul hpp hpb0 hd,
      E213.Lib.Math.NumberTheory.PrimeValuation.vp_mul hpp hm0 hbp,
      hvm, vp_pow hpI hb m₀, hvb, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

/-- Each tail term is divisible by `p^{v_p(d)+1}` (just `v_p(dᵏ) ≥ 2v_p(d) ≥ v_p(d)+1`). -/
theorem R_term_dvd2 (b d m₀ p : Nat) (hpp : Prime213 p) (hpd : p ∣ d) (hd : 0 < d) (k : Nat) :
    p ^ (vp p d + 1) ∣ choose (m₀ + 1) (k + 2) * b ^ ((m₀ + 1) - (k + 2)) * d ^ (k + 2) := by
  have hpI : IsPrime213 p := ⟨hpp.1, hpp.2⟩
  have hv1 : 1 ≤ vp p d := (le_vp_iff p d 1 hpp.1 hd).mp (by rw [Nat.pow_one]; exact hpd)
  have hbnd : vp p d + 1 ≤ (k + 2) * vp p d := by
    have h2v : 2 * vp p d ≤ (k + 2) * vp p d :=
      Nat.mul_le_mul_right (vp p d) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))
    have hstep : vp p d + 1 ≤ 2 * vp p d := by rw [Nat.two_mul]; exact Nat.add_le_add_left hv1 (vp p d)
    exact Nat.le_trans hstep h2v
  have hdd : p ^ (vp p d + 1) ∣ d ^ (k + 2) :=
    dtrans (pow_dvd_of_le p hbnd) (pk_dvd_pow hpI hd (k + 2))
  exact dtrans hdd (dvd_mul_left_nat (choose (m₀ + 1) (k + 2) * b ^ ((m₀ + 1) - (k + 2))))

/-- ★★★★ **Coprime-exponent LTE (succ form)**: for prime `p`, `p ∤ (m₀+1)`, `p ∣ d`, `p ∤ b`,
    `d > 0`,  `v_p((b+d)^{m₀+1} − b^{m₀+1}) = v_p(d)`. -/
theorem lifting_coprime_succ (b d m₀ p : Nat) (hpp : Prime213 p)
    (hpm : ¬ p ∣ (m₀ + 1)) (hpd : p ∣ d) (hpb : ¬ p ∣ b) (hd : 0 < d) :
    vp p ((b + d) ^ (m₀ + 1) - b ^ (m₀ + 1)) = vp p d := by
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hpb (h ▸ ⟨0, rfl⟩))
  have hbp : 0 < b ^ m₀ := Nat.pos_pow_of_pos m₀ hb
  have hmidpos : 0 < (m₀ + 1) * b ^ m₀ * d :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos m₀) hbp) hd
  have hmid : vp p ((m₀ + 1) * b ^ m₀ * d) = vp p d := middle_vp2 b d m₀ p hpp hpm hpb hd
  rw [lte_decomp]
  rcases Nat.eq_zero_or_pos
      (sumTo m₀ (fun k => choose (m₀ + 1) (k + 2) * b ^ ((m₀ + 1) - (k + 2)) * d ^ (k + 2)))
    with hR0 | hRpos
  · rw [hR0, Nat.add_zero]; exact hmid
  · have hR : vp p d + 1
        ≤ vp p (sumTo m₀ (fun k => choose (m₀ + 1) (k + 2) * b ^ ((m₀ + 1) - (k + 2)) * d ^ (k + 2))) :=
      le_vp_sumTo _ hpp.1 hRpos (fun k _ => R_term_dvd2 b d m₀ p hpp hpd hd k)
    rw [vp_add_eq_min hpp.1 hmidpos hRpos (by rw [hmid]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hR)]
    exact hmid

/-- ★★★★ **Coprime-exponent LTE**: for prime `p` with `p ∤ m`, `p ∣ (a−b)`, `p ∤ b`, `b < a`,
    `m ≥ 1`,  `v_p(aᵐ − bᵐ) = v_p(a − b)`. -/
theorem lifting_coprime (a b m p : Nat) (hpp : Prime213 p) (hm : 1 ≤ m) (hpm : ¬ p ∣ m)
    (hba : b < a) (hpd : p ∣ (a - b)) (hpb : ¬ p ∣ b) :
    vp p (a ^ m - b ^ m) = vp p (a - b) := by
  obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, (nat_sub_add_cancel hm).symm⟩
  obtain ⟨d, rfl⟩ : ∃ d, b + d = a := Nat.le.dest (Nat.le_of_lt hba)
  have hbd : (b + d) - b = d := by rw [Nat.add_comm]; exact nat_add_sub_self_right d b
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0, Nat.add_zero] at hba; exact absurd hba (Nat.lt_irrefl b)
    · exact hpos
  rw [hbd] at hpd ⊢
  exact lifting_coprime_succ b d m₀ p hpp hpm hpd hpb hd

end E213.Lib.Math.NumberTheory.LiftingExponentCoprime
