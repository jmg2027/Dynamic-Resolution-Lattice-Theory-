import E213.Lib.Math.NumberTheory.WilsonPlusOne
import E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction
import E213.Lib.Math.NumberTheory.SqrtOneTwoPrimePower

/-!
# Existence side of the Gauss–Wilson `±1` classification (∅-axiom scratch)

`crt_nontrivial_sqrt` builds a nontrivial square root of `1` mod `a*b`
(coprime `a,b > 2`) via `crtSolve a b 1 (b-1)`; `two_pow_nontrivial_sqrt`
builds one for `n = 2^a` (`a ≥ 3`) via `2^(a-1) - 1`.  Feeding either to
`wilson_plus_one_of_nontrivial_sqrt` gives `∏(units of ℤ/n) ≡ +1`.
-/

namespace E213.Lib.Math.NumberTheory.WilsonExistence

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction
  (crtSolve crt_solve_residues)
open E213.Lib.Math.NumberTheory.WilsonPlusOne (wilson_plus_one_of_nontrivial_sqrt)
open E213.Lib.Math.NumberTheory.SqrtOneTwoPrimePower (sqrt_one_coprime)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem (prodMod)
open E213.Lib.Math.NumberTheory.DivisorProductReindex (coprime_mul_dvd)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (mod_eq_of_dvd_sub)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)

/-! ## §0 — small helpers -/

/-- `2 < n → 1 % n = 1`. -/
theorem one_mod_of_two_lt {n : Nat} (hn : 2 < n) : 1 % n = 1 :=
  Nat.mod_eq_of_lt (Nat.lt_trans (by decide) hn)

/-- `(b-1)² ≡ 1 (mod b)` for `b > 2`, stated on the residue directly. -/
theorem pred_sq_mod {b : Nat} (hb : 2 < b) :
    ((b - 1) * (b - 1)) % b = 1 % b := by
  -- write b = c + 3
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 3 := ⟨b - 3, (E213.Tactic.NatHelper.sub_add_cancel hb).symm⟩
  show ((c + 3 - 1) * (c + 3 - 1)) % (c + 3) = 1 % (c + 3)
  have he : c + 3 - 1 = c + 2 := rfl
  rw [he]
  -- (c+2)*(c+2) + (c+3) = 1 + (c+2)*(c+3)
  have hid : (c + 2) * (c + 2) + (c + 3) = 1 + (c + 2) * (c + 3) := by ring_nat
  have h1 : ((c + 2) * (c + 2) + 1 * (c + 3)) % (c + 3) = ((c + 2) * (c + 2)) % (c + 3) :=
    E213.Tactic.NatHelper.add_mul_mod_self_pure ((c + 2) * (c + 2)) (c + 3) 1
  have h1' : (c + 2) * (c + 2) + 1 * (c + 3) = (c + 2) * (c + 2) + (c + 3) := by
    rw [Nat.one_mul]
  rw [h1'] at h1
  have h2 : (1 + (c + 2) * (c + 3)) % (c + 3) = 1 % (c + 3) :=
    E213.Tactic.NatHelper.add_mul_mod_self_pure 1 (c + 3) (c + 2)
  rw [← h1, hid, h2]

/-- `n ∣ (x*x - 1)` from `(x*x) % n = 1 % n` and `0 < x`. -/
theorem dvd_sq_sub_one {n x : Nat} (hn : 0 < n) (hx0 : 0 < x)
    (hsq : (x * x) % n = 1 % n) : n ∣ (x * x - 1) :=
  mod_eq_dvd_sub (x * x) 1 n hn (Nat.mul_pos hx0 hx0) hsq

/-! ## §1 — ★ existence of a nontrivial √1 mod `a*b` (CRT) -/

/-- ★ **Nontrivial square root of `1` mod `a*b`** for coprime `a,b > 2`.
    Witness `x = crtSolve a b 1 (b-1)`: `x ≡ 1 (mod a)`, `x ≡ b-1 (mod b)`. -/
theorem crt_nontrivial_sqrt (a b : Nat) (ha : 2 < a) (hb : 2 < b)
    (hcop : gcd213 a b = 1) :
    ∃ x, x < a * b ∧ gcd213 x (a * b) = 1 ∧ (x * x) % (a * b) = 1 % (a * b)
      ∧ x ≠ 1 ∧ x ≠ a * b - 1 := by
  have hapos : 0 < a := Nat.lt_trans (by decide) ha
  have hbpos : 0 < b := Nat.lt_trans (by decide) hb
  have habpos : 0 < a * b := Nat.mul_pos hapos hbpos
  -- abbreviate the witness
  obtain ⟨x, hxdef⟩ : ∃ x, x = crtSolve a b 1 (b - 1) := ⟨_, rfl⟩
  obtain ⟨hxa, hxb⟩ := crt_solve_residues hcop hapos hbpos 1 (b - 1)
  rw [← hxdef] at hxa hxb
  -- x % a = 1, x % b = b - 1
  have hxa1 : x % a = 1 := by rw [hxa, one_mod_of_two_lt ha]
  have hxbm : x % b = b - 1 := by
    rw [hxb, Nat.mod_eq_of_lt (Nat.sub_lt hbpos (by decide))]
  have hxlt : x < a * b := by rw [hxdef]; exact Nat.mod_lt _ habpos
  -- 0 < x : x % a = 1 ≠ 0, so x ≠ 0
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | hp
    · exfalso; rw [h0] at hxa1
      have : (0 : Nat) % a = 0 := E213.Meta.Nat.AddMod213.zero_mod a
      rw [this] at hxa1; exact absurd hxa1 (by decide)
    · exact hp
  -- (x*x) % a = 1 % a
  have hsq_a : (x * x) % a = 1 % a := by
    rw [mul_mod_pure x x a, hxa1, one_mod_of_two_lt ha]
  -- (x*x) % b = 1 % b
  have hsq_b : (x * x) % b = 1 % b := by
    rw [mul_mod_pure x x b, hxbm]; exact pred_sq_mod hb
  -- a ∣ x*x - 1, b ∣ x*x - 1
  have hda : a ∣ (x * x - 1) := dvd_sq_sub_one hapos hx0 hsq_a
  have hdb : b ∣ (x * x - 1) := dvd_sq_sub_one hbpos hx0 hsq_b
  have hdab : a * b ∣ (x * x - 1) := coprime_mul_dvd hda hdb hcop
  -- (x*x) % (a*b) = 1 % (a*b)
  have hsq_ab : (x * x) % (a * b) = 1 % (a * b) :=
    mod_eq_of_dvd_sub (a * b) (x * x) 1 (Nat.mul_pos hx0 hx0) hdab
  -- coprimality (automatic for a square root of 1)
  have hcop_x : gcd213 x (a * b) = 1 := sqrt_one_coprime (a * b) x habpos hx0 hsq_ab
  refine ⟨x, hxlt, hcop_x, hsq_ab, ?_, ?_⟩
  · -- x ≠ 1 : x % b = b-1 ≠ 1 (b > 2 ⟹ b-1 > 1)
    intro hx1
    rw [hx1] at hxbm
    have h1b : 1 % b = 1 := one_mod_of_two_lt hb
    rw [h1b] at hxbm
    -- 1 = b - 1, but b - 1 > 1 since b > 2
    have hb1 : 2 ≤ b - 1 := by
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 3 := ⟨b - 3, (E213.Tactic.NatHelper.sub_add_cancel hb).symm⟩
      show 2 ≤ c + 3 - 1; exact Nat.le_add_left 2 c
    rw [← hxbm] at hb1; exact absurd hb1 (by decide)
  · -- x ≠ a*b - 1 : (a*b - 1) % a = a - 1, but x % a = 1, and a - 1 ≠ 1 (a > 2)
    intro hxe
    -- (a*b - 1) % a = a - 1
    have hpred_a : (a * b - 1) % a = a - 1 := by
      -- a*b - 1 = a*(b-1) + (a-1)
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 3 := ⟨a - 3, (E213.Tactic.NatHelper.sub_add_cancel ha).symm⟩
      have hbge1 : 1 ≤ b := hbpos
      obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, (Nat.succ_pred_eq_of_pos hbpos).symm⟩
      -- (c+3)*(d+1) - 1 = (c+3)*d + (c+2), and (c+2) < (c+3)
      have hid0 : (c + 3) * (d + 1) = ((c + 2) + d * (c + 3)) + 1 := by ring_nat
      have hid : (c + 3) * (d + 1) - 1 = (c + 2) + d * (c + 3) := by
        rw [hid0]; exact E213.Tactic.NatHelper.add_sub_cancel_right ((c + 2) + d * (c + 3)) 1
      rw [hid, E213.Tactic.NatHelper.add_mul_mod_self_pure (c + 2) (c + 3) d]
      have : c + 2 < c + 3 := Nat.lt_succ_self _
      rw [Nat.mod_eq_of_lt this]
      show c + 2 = c + 3 - 1; rfl
    rw [hxe, hpred_a] at hxa1
    -- a - 1 = 1 with a > 2 is false
    have ha1 : 2 ≤ a - 1 := by
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 3 := ⟨a - 3, (E213.Tactic.NatHelper.sub_add_cancel ha).symm⟩
      show 2 ≤ c + 3 - 1; exact Nat.le_add_left 2 c
    rw [hxa1] at ha1; exact absurd ha1 (by decide)

/-! ## §2 — Wilson `+1` for a coprime split `n = a*b` -/

/-- **Wilson `+1` for a coprime split** `n = a*b`, `a,b > 2` coprime:
    `∏(units of ℤ/(a*b)) ≡ +1 (mod a*b)`. -/
theorem wilson_plus_one_of_coprime_split (a b : Nat) (ha : 2 < a) (hb : 2 < b)
    (hcop : gcd213 a b = 1) :
    prodMod (a * b) (totativeList (a * b)) % (a * b) = 1 % (a * b) := by
  have hapos : 0 < a := Nat.lt_trans (by decide) ha
  have hbpos : 0 < b := Nat.lt_trans (by decide) hb
  -- 1 < a*b : a ≥ 3, b ≥ 3 ⟹ a*b ≥ 9 > 1
  have hn1 : 1 < a * b := by
    have h3a : 3 ≤ a := ha
    have h3b : 3 ≤ b := hb
    have : 3 * 3 ≤ a * b := Nat.mul_le_mul h3a h3b
    exact Nat.lt_of_lt_of_le (by decide) this
  exact wilson_plus_one_of_nontrivial_sqrt (a * b) hn1
    (crt_nontrivial_sqrt a b ha hb hcop)

/-! ## §3 — ★ existence of a nontrivial √1 mod `2^a` (a ≥ 3) -/

/-- ★ **Nontrivial square root of `1` mod `2^a`** for `a ≥ 3`.
    Witness `x = 2^(a-1) - 1`. -/
theorem two_pow_nontrivial_sqrt (a : Nat) (ha : 3 ≤ a) :
    ∃ x, x < 2 ^ a ∧ gcd213 x (2 ^ a) = 1 ∧ (x * x) % (2 ^ a) = 1 % (2 ^ a)
      ∧ x ≠ 1 ∧ x ≠ 2 ^ a - 1 := by
  -- write a = e + 3
  obtain ⟨e, rfl⟩ : ∃ e, a = e + 3 := ⟨a - 3, (E213.Tactic.NatHelper.sub_add_cancel ha).symm⟩
  -- Q := 2^(e+1), with 2^(e+2) = 2*Q and 2^(e+3) = 4*Q
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = 2 ^ (e + 1) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by rw [hQdef]; exact Nat.pos_pow_of_pos (e + 1) (by decide)
  -- 2^(e+2) = 2 * Q
  have hP : 2 ^ (e + 2) = 2 * Q := by
    rw [hQdef, Nat.pow_succ, Nat.mul_comm (2 ^ (e + 1)) 2]
  -- 2^(e+3) = 4 * Q
  have hN : 2 ^ (e + 3) = 4 * Q := by
    rw [Nat.pow_succ, hP]
    show 2 * Q * 2 = 4 * Q
    ring_nat
  -- the witness x = 2^(e+2) - 1 = 2*Q - 1
  obtain ⟨x, hxdef⟩ : ∃ x, x = 2 * Q - 1 := ⟨_, rfl⟩
  have hNpos : 0 < 4 * Q := Nat.mul_pos (by decide) hQpos
  -- Q = q + 1
  obtain ⟨q, hq⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, (Nat.succ_pred_eq_of_pos hQpos).symm⟩
  -- x = 2*Q - 1 = 2*q + 1
  have hx2 : x = 2 * q + 1 := by
    rw [hxdef, hq]
    -- 2*(q+1) - 1 = 2*q + 1
    have h0 : 2 * (q + 1) = (2 * q + 1) + 1 := by ring_nat
    rw [h0]; exact E213.Tactic.NatHelper.add_sub_cancel_right (2 * q + 1) 1
  -- 0 < x
  have hx0 : 0 < x := by rw [hx2]; exact Nat.succ_pos (2 * q)
  -- x*x = 1 + (q)*(4*Q)  (key identity, subtraction-free)
  have hsqid : x * x = 1 + q * (4 * Q) := by
    rw [hx2, hq]
    -- (2q+1)*(2q+1) = 1 + q*(4*(q+1))
    ring_nat
  -- (x*x) % (4*Q) = 1 % (4*Q)
  have hsq : (x * x) % (4 * Q) = 1 % (4 * Q) := by
    rw [hsqid, E213.Tactic.NatHelper.add_mul_mod_self_pure 1 (4 * Q) q]
  -- rephrase modulus as 2^(e+3)
  have hsqN : (x * x) % (2 ^ (e + 3)) = 1 % (2 ^ (e + 3)) := by rw [hN]; exact hsq
  -- coprimality (automatic)
  have h2Npos : 0 < 2 ^ (e + 3) := Nat.pos_pow_of_pos (e + 3) (by decide)
  have hcop_x : gcd213 x (2 ^ (e + 3)) = 1 := sqrt_one_coprime (2 ^ (e + 3)) x h2Npos hx0 hsqN
  -- x < 2^(e+3) : x = 2*Q - 1 < 2*Q ≤ 4*Q = 2^(e+3)
  have hxlt : x < 2 ^ (e + 3) := by
    rw [hN, hxdef]
    have h1 : 2 * Q - 1 < 2 * Q := Nat.sub_lt (Nat.mul_pos (by decide) hQpos) (by decide)
    have h2 : 2 * Q ≤ 4 * Q := Nat.mul_le_mul_right Q (by decide)
    exact Nat.lt_of_lt_of_le h1 h2
  refine ⟨x, hxlt, hcop_x, hsqN, ?_, ?_⟩
  · -- x ≠ 1 : x = 2*Q - 1 with Q ≥ 2 (Q = 2^(e+1) ≥ 2), so x ≥ 3
    intro hx1
    -- Q ≥ 2
    have hQ2 : 2 ≤ Q := by
      rw [hQdef]
      have : 2 ^ 1 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left 1 e)
      exact this
    -- x = 2*q+1, and Q = q+1 ≥ 2 ⟹ q ≥ 1 ⟹ x = 2q+1 ≥ 3
    have hq1 : 1 ≤ q := by
      rw [hq] at hQ2; exact Nat.le_of_succ_le_succ hQ2
    have hx3 : 3 ≤ x := by
      rw [hx2]
      have : 2 * 1 + 1 ≤ 2 * q + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hq1) 1
      exact this
    rw [hx1] at hx3; exact absurd hx3 (by decide)
  · -- x ≠ 2^(e+3) - 1 : x = 2*Q - 1 < 2*Q ≤ 4*Q - 1 = 2^(e+3) - 1
    intro hxe
    -- x < 2*Q, but 2^(e+3) - 1 = 4*Q - 1 ≥ 2*Q  ⟹  x = 2^(e+3)-1 ≥ 2*Q, contra x < 2*Q
    have hx_lt_2Q : x < 2 * Q := by
      rw [hxdef]; exact Nat.sub_lt (Nat.mul_pos (by decide) hQpos) (by decide)
    have h2Q_le : 2 * Q ≤ 2 ^ (e + 3) - 1 := by
      rw [hN]
      -- 2*Q + 1 ≤ 4*Q, and 4*Q = (4*Q - 1) + 1, so 2*Q ≤ 4*Q - 1
      have h2Q1 : 1 ≤ 2 * Q := Nat.mul_pos (by decide) hQpos
      have hstep : 2 * Q + 1 ≤ 4 * Q := by
        have heq : (4 : Nat) * Q = 2 * Q + 2 * Q := by ring_nat
        rw [heq]; exact Nat.add_le_add_left h2Q1 (2 * Q)
      -- 1 ≤ 4*Q
      have h4Q1 : 1 ≤ 4 * Q := Nat.mul_pos (by decide) hQpos
      have hsac : (4 * Q - 1) + 1 = 4 * Q := E213.Tactic.NatHelper.sub_add_cancel h4Q1
      -- 2*Q + 1 ≤ (4*Q - 1) + 1  ⟹  2*Q ≤ 4*Q - 1
      rw [← hsac] at hstep
      exact Nat.le_of_succ_le_succ hstep
    rw [hxe] at hx_lt_2Q
    exact absurd hx_lt_2Q (Nat.not_lt.mpr h2Q_le)

/-- **Wilson `+1` for `n = 2^a`**, `a ≥ 3`:
    `∏(units of ℤ/2^a) ≡ +1 (mod 2^a)`. -/
theorem wilson_plus_one_two_pow (a : Nat) (ha : 3 ≤ a) :
    prodMod (2 ^ a) (totativeList (2 ^ a)) % (2 ^ a) = 1 % (2 ^ a) := by
  have hn1 : 1 < 2 ^ a := by
    have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (Nat.le_trans (by decide) ha)
    exact Nat.lt_of_lt_of_le (by decide) this
  exact wilson_plus_one_of_nontrivial_sqrt (2 ^ a) hn1 (two_pow_nontrivial_sqrt a ha)

/-! ## §4 — smokes (`decide` on closed numerals) -/

/-- `crt_nontrivial_sqrt` at `a=3, b=5` (n=15): `crtSolve 3 5 1 4 = 4`, a √1 ∈ {4,11}. -/
theorem smoke_crt_15 :
    crtSolve 3 5 1 4 = 4 ∧ (4 * 4) % 15 = 1 % 15 ∧ (4 : Nat) ≠ 1 ∧ (4 : Nat) ≠ 14 := by
  decide

/-- `wilson_plus_one_of_coprime_split` at n=15: `∏(units) ≡ 1 (mod 15)`. -/
theorem smoke_split_15 :
    prodMod 15 (totativeList 15) % 15 = 1 % 15 := by decide

/-- `wilson_plus_one_of_coprime_split` at n=21 (`3·7`): `∏(units) ≡ 1 (mod 21)`. -/
theorem smoke_split_21 :
    prodMod 21 (totativeList 21) % 21 = 1 % 21 := by decide

/-- `wilson_plus_one_two_pow` at n=8: `∏(units of ℤ/8) ≡ 1 (mod 8)`. -/
theorem smoke_two_pow_8 :
    prodMod 8 (totativeList 8) % 8 = 1 % 8 := by decide

/-- `wilson_plus_one_two_pow` at n=16: `∏(units of ℤ/16) ≡ 1 (mod 16)`. -/
theorem smoke_two_pow_16 :
    prodMod 16 (totativeList 16) % 16 = 1 % 16 := by decide

/-- `two_pow_nontrivial_sqrt` witness at a=3 (n=8): `2^2 - 1 = 3`, `3² ≡ 1 mod 8`. -/
theorem smoke_two_pow_witness_8 :
    (2 ^ (3 - 1) - 1 : Nat) = 3 ∧ (3 * 3) % 8 = 1 % 8 ∧ (3 : Nat) ≠ 1 ∧ (3 : Nat) ≠ 7 := by
  decide

end E213.Lib.Math.NumberTheory.WilsonExistence
