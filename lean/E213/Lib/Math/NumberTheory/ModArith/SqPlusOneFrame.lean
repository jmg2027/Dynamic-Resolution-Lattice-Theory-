import E213.Lib.Math.NumberTheory.ModArith.QRNegOne
import E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor

/-!
# SqPlusOneFrame — when is `x² + 1` reducible mod `p`?  (∅-axiom)

The **frame-visibility** brick of the number-system square (`research-notes/
frontiers/numbersystem_square.md` T4): for an odd prime `p`,

> `(∃ x, p ∣ x² + 1)  ↔  p ≡ 1 (mod 4)`

— the first supplement to quadratic reciprocity / Fermat's two-square criterion,
in clean reducibility form.  `−1` has a square root mod `p` exactly when
`p ≡ 1 (mod 4)`.

Assembled from the two halves already in the corpus: the Gaussian pillar
`QRNegOne.qr_neg_one` (`p ≡ 1 mod 4 ⟹ ∃ x, p ∣ x²+1`, the harder Lagrange-bound
direction) and the Euler-criterion iff `EulerFirstSupplement.neg_one_qr_iff`
(bounded form `∃ x, 1≤x<p ∧ x²%p = p−1 ↔ p%4=1`).  The bridge reduces an unbounded
root `x` to the bounded witness `x % p` via `MarkovPrimeFactor.root_mod_P`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.SqPlusOneFrame

open E213.Lib.Math.NumberTheory.ModArith.QRNegOne (qr_neg_one)
open E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement (neg_one_qr_iff)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (root_mod_P)
open E213.Meta.Nat.AddMod213 (div_add_mod mod_add_mod)
open E213.Tactic.NatHelper (add_sub_cancel_right)

/-- `(s + 1) % p = 0` (`p > 1`) ⟹ `s % p = p − 1`: the predecessor reading of a
    root of `−1`.  `s % p < p` and `(s%p + 1) % p = 0`, so `s%p + 1 = p`. -/
theorem mod_pred_of_succ_mod_zero {p s : Nat} (hp : 1 < p) (h : (s + 1) % p = 0) :
    s % p = p - 1 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hlt : s % p < p := Nat.mod_lt s hppos
  have hstep : (s % p + 1) % p = 0 := by rw [mod_add_mod hppos s 1]; exact h
  rcases Nat.lt_or_ge (s % p + 1) p with hcase | hcase
  · exact absurd ((Nat.mod_eq_of_lt hcase).symm.trans hstep) (fun hh => Nat.noConfusion hh)
  · have heq : s % p + 1 = p := Nat.le_antisymm (Nat.succ_le_of_lt hlt) hcase
    have hc : (s % p + 1) - 1 = p - 1 := congrArg (· - 1) heq
    rwa [add_sub_cancel_right] at hc

/-- ★★★★★ **Frame visibility: `x² + 1` is reducible mod an odd prime `p` iff
    `p ≡ 1 (mod 4)`.**  The first supplement to quadratic reciprocity in clean
    reducibility form — `−1` is a QR mod `p` exactly when `p % 4 = 1`. -/
theorem sq_plus_one_dvd_iff (p : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hodd : p % 2 = 1) :
    (∃ x : Nat, p ∣ (x * x + 1)) ↔ p % 4 = 1 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  obtain ⟨m, hm⟩ : ∃ m, 2 * m = p - 1 := by
    refine ⟨p / 2, ?_⟩
    have hdm : 2 * (p / 2) + p % 2 = p := div_add_mod p 2
    rw [hodd] at hdm
    have hc : (2 * (p / 2) + 1) - 1 = p - 1 := congrArg (· - 1) hdm
    rwa [add_sub_cancel_right] at hc
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hm
      exact absurd (Nat.le_of_sub_eq_zero hm.symm) (Nat.not_le.mpr hp)
    · exact h0
  constructor
  · rintro ⟨x, hx⟩
    refine (neg_one_qr_iff p m hp hpr hm hm1).mp ⟨x % p, ?_, Nat.mod_lt x hppos, ?_⟩
    · have hroot := root_mod_P p x hp hx
      rcases Nat.eq_zero_or_pos (x % p) with h0 | h0
      · have e : (x % p) * (x % p) + 1 = 1 := by rw [h0]
        have h1 : (1 : Nat) % p = 0 := (congrArg (· % p) e).symm.trans hroot
        exact absurd ((Nat.mod_eq_of_lt hp).symm.trans h1) (by decide)
      · exact h0
    · have hroot := root_mod_P p x hp hx
      have hsq : (x % p) ^ 2 = (x % p) * (x % p) := Nat.pow_two (x % p)
      rw [hsq]
      exact mod_pred_of_succ_mod_zero hp hroot
  · intro h4
    exact qr_neg_one p hp hpr h4

end E213.Lib.Math.NumberTheory.ModArith.SqPlusOneFrame
