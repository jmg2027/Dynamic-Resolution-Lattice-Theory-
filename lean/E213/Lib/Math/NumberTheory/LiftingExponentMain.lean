import E213.Lib.Math.NumberTheory.BinomialTwoVar
import E213.Lib.Math.NumberTheory.LiftingExponentPP
import E213.Lib.Math.NumberTheory.ModArith.LucasTheorem

/-!
# Lifting-the-exponent: the prime-power kernel `v_p(aᵖ − bᵖ) = v_p(a−b) + 1` (∅-axiom)

The hard kernel of LTE, for an odd prime `p` (`3 ≤ p`) with `p ∣ (a−b)`, `p ∤ b`.  Binomial route:
write `a = b + d` (`d = a−b`); the two-variable binomial theorem gives

> `(b+d)ᵖ − bᵖ = p·b^{p−1}·d + R`,   `R = Σ_{k=2}^{p} C(p,k) b^{p−k} dᵏ`.

The middle term has `v_p = v_p(d)+1`; every tail term has `v_p ≥ v_p(d)+2` (since `p ∣ C(p,k)` for
`0<k<p`, and the `k=p` term `dᵖ` has `v_p = p·v_p(d) ≥ v_p(d)+2` using `p ≥ 3`).  The strict-minimum
valuation law `vp_add_eq_min` then pins `v_p((b+d)ᵖ − bᵖ) = v_p(d)+1`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.LiftingExponentMain

open E213.Lib.Math.NumberTheory.BinomialTwoVar (binom2 add_pow)
open E213.Lib.Math.NumberTheory.LiftingExponentPP (vp_add_eq_min le_vp_sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_self choose_zero_right choose_one_right)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_split_first)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.ModArith.LucasTheorem (prime_dvd_choose)
open E213.Meta.Nat.Valuation (vp pow_vp_dvd le_vp_iff pow_dvd_of_le dtrans)
open E213.Meta.Nat.VpMul (vp_pow vp_self_pow IsPrime213)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Meta.Nat.NatRing213 (nat_add_sub_self_right nat_sub_add_cancel)

/-! ## §1 — ℕ divisibility / valuation helpers -/

theorem mul_dvd_mul_nat {a b c e : Nat} (h1 : a ∣ b) (h2 : c ∣ e) : a * c ∣ b * e := by
  obtain ⟨w1, hw1⟩ := h1; obtain ⟨w2, hw2⟩ := h2
  exact ⟨w1 * w2, by rw [hw1, hw2]; ring_nat⟩

theorem dvd_mul_right_nat {x y : Nat} (h : x ∣ y) (z : Nat) : x ∣ y * z := by
  obtain ⟨w, hw⟩ := h; exact ⟨w * z, by rw [hw]; ring_nat⟩

theorem dvd_of_eq_nat {x y z : Nat} (h : y = z) (hd : x ∣ y) : x ∣ z := h ▸ hd

theorem pk_dvd_pow {p a : Nat} (hp : IsPrime213 p) (ha : 0 < a) (m : Nat) :
    p ^ (m * vp p a) ∣ a ^ m := by
  rw [← vp_pow hp ha m]; exact pow_vp_dvd p (a ^ m)

/-! ## §2 — decomposition `(b+d)ᵖ − bᵖ = p·b^{p−1}·d + R` -/

/-- `binom2 b d (p₀+1) = b^{p₀+1} + (the k≥1 tail)`. -/
theorem binom2_extract_b (b d p₀ : Nat) :
    binom2 b d (p₀ + 1)
      = b ^ (p₀ + 1)
        + sumTo (p₀ + 1) (fun k => choose (p₀ + 1) (k + 1) * b ^ ((p₀ + 1) - (k + 1)) * d ^ (k + 1)) := by
  show sumTo (p₀ + 2) (fun k => choose (p₀ + 1) k * b ^ ((p₀ + 1) - k) * d ^ k) = _
  rw [sumTo_split_first (p₀ + 1) (fun k => choose (p₀ + 1) k * b ^ ((p₀ + 1) - k) * d ^ k)]
  show choose (p₀ + 1) 0 * b ^ ((p₀ + 1) - 0) * d ^ 0 + _ = b ^ (p₀ + 1) + _
  rw [choose_zero_right, Nat.sub_zero, Nat.pow_zero]
  show 1 * b ^ (p₀ + 1) * 1 + _ = b ^ (p₀ + 1) + _
  rw [Nat.one_mul, Nat.mul_one]

/-- ★★ **Decomposition**: `(b+d)^{p₀+1} − b^{p₀+1} = (p₀+1)·b^{p₀}·d + R`. -/
theorem lte_decomp (b d p₀ : Nat) :
    (b + d) ^ (p₀ + 1) - b ^ (p₀ + 1)
      = (p₀ + 1) * b ^ p₀ * d
        + sumTo p₀ (fun k => choose (p₀ + 1) (k + 2) * b ^ ((p₀ + 1) - (k + 2)) * d ^ (k + 2)) := by
  rw [add_pow, binom2_extract_b]
  rw [Nat.add_comm (b ^ (p₀ + 1)) _, nat_add_sub_self_right _ (b ^ (p₀ + 1))]
  rw [sumTo_split_first p₀ (fun k => choose (p₀ + 1) (k + 1) * b ^ ((p₀ + 1) - (k + 1)) * d ^ (k + 1))]
  show choose (p₀ + 1) (0 + 1) * b ^ ((p₀ + 1) - (0 + 1)) * d ^ (0 + 1) + _
     = (p₀ + 1) * b ^ p₀ * d + _
  rw [choose_one_right]
  show (p₀ + 1) * b ^ ((p₀ + 1) - (0 + 1)) * d ^ (0 + 1) + _ = (p₀ + 1) * b ^ p₀ * d + _
  rw [show (p₀ + 1) - (0 + 1) = p₀ from rfl, Nat.pow_one]

/-! ## §3 — the tail valuation bound -/

/-- Each tail term is divisible by `p^{v_p(d)+2}` (the crux: `p ∣ C(p,k)` + `v_p(d) ≥ 1`). -/
theorem R_term_dvd (b d p₀ : Nat) (hp : Prime213 (p₀ + 1)) (hp3 : 3 ≤ p₀ + 1)
    (hpd : (p₀ + 1) ∣ d) (hd : 0 < d) (k : Nat) (hk : k < p₀) :
    (p₀ + 1) ^ (vp (p₀ + 1) d + 2)
      ∣ choose (p₀ + 1) (k + 2) * b ^ ((p₀ + 1) - (k + 2)) * d ^ (k + 2) := by
  have hpI : IsPrime213 (p₀ + 1) := ⟨hp.1, hp.2⟩
  have hp2 : 2 ≤ p₀ + 1 := hp.1
  have hv1 : 1 ≤ vp (p₀ + 1) d := (le_vp_iff (p₀ + 1) d 1 hp2 hd).mp (by rw [Nat.pow_one]; exact hpd)
  have hk2p : k + 2 ≤ p₀ + 1 := Nat.succ_le_succ hk
  rcases Nat.lt_or_ge (k + 2) (p₀ + 1) with hlt | hge
  · have hch : (p₀ + 1) ∣ choose (p₀ + 1) (k + 2) := prime_dvd_choose hp (Nat.succ_pos (k + 1)) hlt
    have hbnd : vp (p₀ + 1) d + 1 ≤ (k + 2) * vp (p₀ + 1) d := by
      have h2v : 2 * vp (p₀ + 1) d ≤ (k + 2) * vp (p₀ + 1) d :=
        Nat.mul_le_mul_right (vp (p₀ + 1) d) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))
      have hstep : vp (p₀ + 1) d + 1 ≤ 2 * vp (p₀ + 1) d := by
        rw [Nat.two_mul]; exact Nat.add_le_add_left hv1 (vp (p₀ + 1) d)
      exact Nat.le_trans hstep h2v
    have hdd : (p₀ + 1) ^ (vp (p₀ + 1) d + 1) ∣ d ^ (k + 2) :=
      dtrans (pow_dvd_of_le (p₀ + 1) hbnd) (pk_dvd_pow hpI hd (k + 2))
    have hcombine : (p₀ + 1) ^ (vp (p₀ + 1) d + 2) ∣ choose (p₀ + 1) (k + 2) * d ^ (k + 2) := by
      have hmm := mul_dvd_mul_nat hch hdd
      rw [show vp (p₀ + 1) d + 2 = 1 + (vp (p₀ + 1) d + 1) from by ring_nat, pow_add, Nat.pow_one]
      exact hmm
    refine dvd_of_eq_nat ?_ (dvd_mul_right_nat hcombine (b ^ ((p₀ + 1) - (k + 2))))
    ring_nat
  · have hkeq : k + 2 = p₀ + 1 := Nat.le_antisymm hk2p hge
    rw [hkeq, choose_self, Nat.sub_self, Nat.pow_zero]
    have hbnd2 : vp (p₀ + 1) d + 2 ≤ (p₀ + 1) * vp (p₀ + 1) d := by
      have h3v : 3 * vp (p₀ + 1) d ≤ (p₀ + 1) * vp (p₀ + 1) d :=
        Nat.mul_le_mul_right (vp (p₀ + 1) d) hp3
      have hstep : vp (p₀ + 1) d + 2 ≤ 3 * vp (p₀ + 1) d := by
        rw [show (3 : Nat) * vp (p₀ + 1) d
              = vp (p₀ + 1) d + (vp (p₀ + 1) d + vp (p₀ + 1) d) from by ring_nat]
        exact Nat.add_le_add_left
          (Nat.le_trans (by decide : 2 ≤ 1 + 1) (Nat.add_le_add hv1 hv1)) (vp (p₀ + 1) d)
      exact Nat.le_trans hstep h3v
    have hdp : (p₀ + 1) ^ (vp (p₀ + 1) d + 2) ∣ d ^ (p₀ + 1) :=
      dtrans (pow_dvd_of_le (p₀ + 1) hbnd2) (pk_dvd_pow hpI hd (p₀ + 1))
    refine dvd_of_eq_nat ?_ hdp
    show d ^ (p₀ + 1) = 1 * 1 * d ^ (p₀ + 1)
    ring_nat

/-! ## §4 — the middle term valuation -/

/-- `v_p((p₀+1)·b^{p₀}·d) = v_p(d) + 1` (using `p ∤ b`, so `v_p(b)=0`, and `v_p(p)=1`). -/
theorem middle_vp (b d p₀ : Nat) (hp : Prime213 (p₀ + 1))
    (hpb : ¬ (p₀ + 1) ∣ b) (hd : 0 < d) :
    vp (p₀ + 1) ((p₀ + 1) * b ^ p₀ * d) = vp (p₀ + 1) d + 1 := by
  have hpI : IsPrime213 (p₀ + 1) := ⟨hp.1, hp.2⟩
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hpb (h ▸ ⟨0, rfl⟩))
  have hbp : 0 < b ^ p₀ := Nat.pos_pow_of_pos p₀ hb
  have hp0 : 0 < p₀ + 1 := Nat.succ_pos p₀
  have hpb0 : 0 < (p₀ + 1) * b ^ p₀ := Nat.mul_pos hp0 hbp
  have hself : vp (p₀ + 1) (p₀ + 1) = 1 := by
    have h := vp_self_pow hpI 1; rwa [Nat.pow_one] at h
  have hvb : vp (p₀ + 1) b = 0 := vp_eq_zero_of_not_dvd hpI hb hpb
  rw [E213.Lib.Math.NumberTheory.PrimeValuation.vp_mul hp hpb0 hd,
      E213.Lib.Math.NumberTheory.PrimeValuation.vp_mul hp hp0 hbp,
      hself, vp_pow hpI hb p₀, hvb, Nat.mul_zero, Nat.add_zero, Nat.add_comm]

/-! ## §5 — assembly -/

/-- ★★★★★ **Prime-power lifting (succ form)**: for `p = p₀+1` an odd prime (`3 ≤ p`) with
    `p ∣ d`, `p ∤ b`, `d > 0`,  `v_p((b+d)ᵖ − bᵖ) = v_p(d) + 1`. -/
theorem lifting_succ (b d p₀ : Nat) (hp : Prime213 (p₀ + 1)) (hp3 : 3 ≤ p₀ + 1)
    (hpd : (p₀ + 1) ∣ d) (hpb : ¬ (p₀ + 1) ∣ b) (hd : 0 < d) :
    vp (p₀ + 1) ((b + d) ^ (p₀ + 1) - b ^ (p₀ + 1)) = vp (p₀ + 1) d + 1 := by
  have hp2 : 2 ≤ p₀ + 1 := hp.1
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hpb (h ▸ ⟨0, rfl⟩))
  have hbp : 0 < b ^ p₀ := Nat.pos_pow_of_pos p₀ hb
  have hmidpos : 0 < (p₀ + 1) * b ^ p₀ * d :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos p₀) hbp) hd
  have hmid : vp (p₀ + 1) ((p₀ + 1) * b ^ p₀ * d) = vp (p₀ + 1) d + 1 := middle_vp b d p₀ hp hpb hd
  rw [lte_decomp]
  rcases Nat.eq_zero_or_pos
      (sumTo p₀ (fun k => choose (p₀ + 1) (k + 2) * b ^ ((p₀ + 1) - (k + 2)) * d ^ (k + 2)))
    with hR0 | hRpos
  · rw [hR0, Nat.add_zero]; exact hmid
  · have hR : vp (p₀ + 1) d + 2
        ≤ vp (p₀ + 1) (sumTo p₀ (fun k => choose (p₀ + 1) (k + 2) * b ^ ((p₀ + 1) - (k + 2)) * d ^ (k + 2))) :=
      le_vp_sumTo _ hp2 hRpos (fun k hk => R_term_dvd b d p₀ hp hp3 hpd hd k hk)
    rw [vp_add_eq_min hp2 hmidpos hRpos (by rw [hmid]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hR)]
    exact hmid

/-- ★★★★★ **Prime-power lifting**: for an odd prime `p` (`3 ≤ p`) with `p ∣ (a−b)`, `p ∤ b`,
    `b < a`,  `v_p(aᵖ − bᵖ) = v_p(a − b) + 1`.  The hard kernel of lifting-the-exponent. -/
theorem lifting_prime_power (a b p : Nat) (hp : Prime213 p) (hp3 : 3 ≤ p)
    (hba : b < a) (hpd : p ∣ (a - b)) (hpb : ¬ p ∣ b) :
    vp p (a ^ p - b ^ p) = vp p (a - b) + 1 := by
  have h1p : 1 ≤ p := Nat.le_trans (by decide) hp.1
  obtain ⟨p₀, rfl⟩ : ∃ p₀, p = p₀ + 1 := ⟨p - 1, (nat_sub_add_cancel h1p).symm⟩
  obtain ⟨d, rfl⟩ : ∃ d, b + d = a := Nat.le.dest (Nat.le_of_lt hba)
  have hbd : (b + d) - b = d := by rw [Nat.add_comm]; exact nat_add_sub_self_right d b
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0, Nat.add_zero] at hba; exact absurd hba (Nat.lt_irrefl b)
    · exact hpos
  rw [hbd] at hpd ⊢
  exact lifting_succ b d p₀ hp hp3 hpd hpb hd

end E213.Lib.Math.NumberTheory.LiftingExponentMain
