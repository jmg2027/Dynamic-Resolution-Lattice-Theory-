import E213.Lib.Math.NumberTheory.ModArith.SecondSupplement
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor

/-!
# The `x² − 2` second-supplement frame (∅-axiom)

`(∃ x, p ∣ x² − 2) ↔ (m − m/2) % 2 = 0` for an odd prime `p = 2m + 1` —
the quadratic-residue criterion for `2` (the **second supplement** to
quadratic reciprocity), framed as a divisibility-of-`x²−2` statement.

This is the genuine sibling of `SqPlusOneFrame` (the `x²+1`/first
supplement, T4 `(∃x, p∣x²+1) ↔ p%4=1`).  The bridge is identical in
shape: an *unbounded* witness root `x` is reduced to the *bounded*
residue `x % p` via `dvd_sq_sub_mod_sq` + `dvd_sub_213`, the extra
`r² ≥ 2` lower bound is recovered (the `−2` shift, absent in the `+1`
frame), and the residue is fed to `second_supplement_m`.

All ∅-axiom: `omega`/`simp`/propext-leaking `rw…at` are avoided
throughout; subtraction friction is dissolved with the NatHelper PURE
twins (`sub_add_cancel`, `add_sub_cancel_right`, `le_sub_of_add_le`,
`sub_le_sub_left`, `zero_mod`).
-/

namespace E213.Lib.Math.NumberTheory.ModArith.SqMinusTwoFrame

open E213.Lib.Math.NumberTheory.ModArith.SecondSupplement (second_supplement_m)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (dvd_sq_sub_mod_sq)
open E213.Meta.Nat.Gcd213 (dvd_sub_213)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.NatHelper (add_sub_cancel_right sub_add_cancel add_mul_mod_self_pure
  le_sub_of_add_le sub_le_sub_left zero_mod)

/-- Bridge: an unbounded root `x` of `x² ≡ 2 (mod p)` descends to the bounded
    residue `x % p`, which satisfies `(x%p)² ≡ 2 (mod p)`. -/
theorem root_mod_P_sub_two (p x : Nat) (hp2 : 2 < p) (h2x : 2 ≤ x * x)
    (hpx : p ∣ (x * x - 2)) : (x % p) * (x % p) % p = 2 := by
  have hdr : p ∣ (x * x - (x % p) * (x % p)) := dvd_sq_sub_mod_sq p x
  have hrle : (x % p) * (x % p) ≤ x * x :=
    Nat.mul_le_mul (Nat.mod_le x p) (Nat.mod_le x p)
  have hr2 : 2 ≤ (x % p) * (x % p) := by
    rcases Nat.lt_or_ge ((x % p) * (x % p)) 2 with hlt | hge
    · exfalso
      have hr2le2 : (x % p) * (x % p) ≤ 2 := Nat.le_of_lt hlt
      have horder : (x * x - 2) ≤ (x * x - (x % p) * (x % p)) :=
        sub_le_sub_left (x * x) hr2le2
      have hdsub : p ∣ ((x * x - (x % p) * (x % p)) - (x * x - 2)) :=
        dvd_sub_213 _ _ p horder hpx hdr
      have heq : (x * x - (x % p) * (x % p)) - (x * x - 2) = 2 - (x % p) * (x % p) := by
        have hcancel1 : (x * x - 2) + 2 = x * x := sub_add_cancel h2x
        have hcancel2 : (2 - (x % p) * (x % p)) + (x % p) * (x % p) = 2 :=
          sub_add_cancel hr2le2
        have hsum : ((2 - (x % p) * (x % p)) + (x * x - 2)) + (x % p) * (x % p)
            = x * x := by
          calc ((2 - (x % p) * (x % p)) + (x * x - 2)) + (x % p) * (x % p)
              = (x * x - 2) + ((2 - (x % p) * (x % p)) + (x % p) * (x % p)) := by ring_nat
            _ = (x * x - 2) + 2 := by rw [hcancel2]
            _ = x * x := hcancel1
        have hcong : ((2 - (x % p) * (x % p)) + (x * x - 2)) + (x % p) * (x % p)
              - (x % p) * (x % p)
            = x * x - (x % p) * (x % p) := congrArg (· - (x % p) * (x % p)) hsum
        have hback : x * x - (x % p) * (x % p)
            = ((2 - (x % p) * (x % p)) + (x * x - 2)) := by
          rw [add_sub_cancel_right] at hcong; exact hcong.symm
        have hcong2 : (x * x - (x % p) * (x % p)) - (x * x - 2)
            = ((2 - (x % p) * (x % p)) + (x * x - 2)) - (x * x - 2) :=
          congrArg (· - (x * x - 2)) hback
        rw [add_sub_cancel_right] at hcong2
        exact hcong2
      have hpos : 1 ≤ 2 - (x % p) * (x % p) := by
        have hr1 : (x % p) * (x % p) ≤ 1 := Nat.le_of_lt_succ hlt
        have hadd : 1 + (x % p) * (x % p) ≤ 2 := by
          calc 1 + (x % p) * (x % p) ≤ 1 + 1 := Nat.add_le_add_left hr1 1
            _ = 2 := by decide
        exact le_sub_of_add_le hadd
      have hsmall : 2 - (x % p) * (x % p) ≤ 2 := Nat.sub_le 2 _
      obtain ⟨w, hw⟩ := hdsub
      rw [heq] at hw
      have hple : p ≤ p * w := by
        rcases Nat.eq_zero_or_pos w with h0 | hwpos
        · exfalso
          rw [h0, Nat.mul_zero] at hw
          exact absurd (hw ▸ hpos) (by decide)
        · calc p = p * 1 := (Nat.mul_one p).symm
            _ ≤ p * w := Nat.mul_le_mul_left p hwpos
      have hp2le : p ≤ 2 := Nat.le_trans hple (hw ▸ hsmall)
      exact absurd (Nat.lt_of_lt_of_le hp2 hp2le) (Nat.lt_irrefl 2)
    · exact hge
  have horder : (x * x - (x % p) * (x % p)) ≤ (x * x - 2) :=
    sub_le_sub_left (x * x) hr2
  have hdsub : p ∣ ((x * x - 2) - (x * x - (x % p) * (x % p))) :=
    dvd_sub_213 _ _ p horder hdr hpx
  have heq : (x * x - 2) - (x * x - (x % p) * (x % p)) = (x % p) * (x % p) - 2 := by
    have hcancelR : (x * x - (x % p) * (x % p)) + (x % p) * (x % p) = x * x :=
      sub_add_cancel hrle
    have hcancel2 : ((x % p) * (x % p) - 2) + 2 = (x % p) * (x % p) :=
      sub_add_cancel hr2
    have hsum : (((x % p) * (x % p) - 2) + (x * x - (x % p) * (x % p))) + 2
        = x * x := by
      calc (((x % p) * (x % p) - 2) + (x * x - (x % p) * (x % p))) + 2
          = (x * x - (x % p) * (x % p)) + (((x % p) * (x % p) - 2) + 2) := by ring_nat
        _ = (x * x - (x % p) * (x % p)) + (x % p) * (x % p) := by rw [hcancel2]
        _ = x * x := hcancelR
    have hcong : (((x % p) * (x % p) - 2) + (x * x - (x % p) * (x % p))) + 2 - 2
        = x * x - 2 := congrArg (· - 2) hsum
    have hback : x * x - 2
        = ((x % p) * (x % p) - 2) + (x * x - (x % p) * (x % p)) := by
      rw [add_sub_cancel_right] at hcong; exact hcong.symm
    have hcong2 : (x * x - 2) - (x * x - (x % p) * (x % p))
        = (((x % p) * (x % p) - 2) + (x * x - (x % p) * (x % p)))
            - (x * x - (x % p) * (x % p)) :=
      congrArg (· - (x * x - (x % p) * (x % p))) hback
    rw [add_sub_cancel_right] at hcong2
    exact hcong2
  obtain ⟨w, hw⟩ := hdsub
  rw [heq] at hw
  have hrr : (x % p) * (x % p) = 2 + w * p := by
    have hcancel : ((x % p) * (x % p) - 2) + 2 = (x % p) * (x % p) :=
      sub_add_cancel hr2
    calc (x % p) * (x % p) = ((x % p) * (x % p) - 2) + 2 := hcancel.symm
      _ = p * w + 2 := by rw [hw]
      _ = 2 + w * p := by ring_nat
  have hmod : (x % p) * (x % p) % p = 2 % p := by
    rw [hrr]; exact add_mul_mod_self_pure 2 p w
  rw [hmod]
  exact Nat.mod_eq_of_lt hp2

/-- ★★★ **Second-supplement frame** for `x² − 2`: for an odd prime `p = 2m + 1`,
    `2` is a quadratic residue mod `p` (i.e. some `x` has `p ∣ x² − 2`) iff
    `(m − m/2) % 2 = 0`. -/
theorem sq_minus_two_dvd_iff (p m : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m)
    (hp2 : 2 < p) :
    (∃ x : Nat, 2 ≤ x * x ∧ p ∣ (x * x - 2)) ↔ (m - m / 2) % 2 = 0 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  constructor
  · rintro ⟨x, h2x, hx⟩
    refine (second_supplement_m p m hp hpr h2m hm1 hp2).mp ⟨x % p, ?_, Nat.mod_lt x hppos, ?_⟩
    · rcases Nat.eq_zero_or_pos (x % p) with h0 | hpos
      · exfalso
        have hroot := root_mod_P_sub_two p x hp2 h2x hx
        have e : (x % p) * (x % p) % p = 0 := by
          rw [h0, Nat.zero_mul]; exact zero_mod p
        exact absurd (e.symm.trans hroot) (by decide)
      · exact hpos
    · have hroot := root_mod_P_sub_two p x hp2 h2x hx
      have hsq : (x % p) ^ 2 = (x % p) * (x % p) := Nat.pow_two (x % p)
      rw [hsq]; exact hroot
  · intro hrhs
    obtain ⟨z, _, hzlt, hzsq⟩ := (second_supplement_m p m hp hpr h2m hm1 hp2).mpr hrhs
    have hsq : z ^ 2 = z * z := Nat.pow_two z
    have hzz : z * z % p = 2 := by rw [← hsq]; exact hzsq
    have h2le : 2 ≤ z * z := by
      have hmle : z * z % p ≤ z * z := Nat.mod_le (z * z) p
      rw [hzz] at hmle; exact hmle
    refine ⟨z, h2le, ?_⟩
    have hdm : p * (z * z / p) + z * z % p = z * z := div_add_mod (z * z) p
    refine ⟨z * z / p, ?_⟩
    have hstep : p * (z * z / p) + 2 = z * z := by rw [← hzz]; exact hdm
    have hcong : p * (z * z / p) + 2 - 2 = z * z - 2 := congrArg (· - 2) hstep
    rw [add_sub_cancel_right] at hcong
    exact hcong.symm

end E213.Lib.Math.NumberTheory.ModArith.SqMinusTwoFrame
