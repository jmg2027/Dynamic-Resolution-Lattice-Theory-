import E213.Lib.Math.NumberSystems.Rat213
import E213.Meta.Int213.Bound

/-!
# CompletionDichotomy — collapse vs rigid axis, the archimedean witness

`theory/math/numbersystems/slot_arithmetic.md` (collapse-vs-rigid): a pair-Lens
extension either **collapses** (the obstruction readout is valued in
the old data, so the pair quotient is total — ℕ→ℤ→ℚ, dimension stays
1) or stays a **rigid axis** — and the dichotomy is a property of the
**(question, frame) pair**, not of the question alone.

This file pins the archimedean side for `x² = −1`: there is no
rational solution, and the reason is order-positivity — two integer
squares sum to zero only at the origin (`int_sumSq_eq_zero`), the
anisotropy of the ℤ[i] / ℂ norm `a² + b²` **at the real place**.  The
∣-frames split: `ModArith/QRNegOne.qr_neg_one` (PURE) sees `x² = −1`
at every prime `p ≡ 1 (mod 4)` (`2² + 1 = 5`), and the `Padic/`
Hensel kit lifts the witness — the extension *collapses* 5-adically.
Visibility per frame is the Legendre symbol; the rigidity below is
the certificate at the order frame and the `p ≡ 3 (mod 4)` frames.

Contrast — the *order-visible* obstruction `x² = 2`: located by a
sandwich of rationals (absorbed by the order completion ℝ,
`Irrational/Sqrt2Cut`), yet algebra-invisible over ℚ (rigid 2-dim
ℚ(√2)).  Both questions are frame-relative; they differ in *which*
frames see them.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.CompletionDichotomy

open E213.Meta.Int213 (add_left_neg int_sq_nonneg)
open E213.Lib.Math.NumberSystems.Rat213 (ratioEqZ)

/-- ★★★★ **Two integer squares sum to zero only at the origin** — the
    anisotropy of the `a² + b²` form (the ℤ[i] / ℂ norm).  PURE via
    `int_sq_nonneg` + `add_eq_zero_of_nonneg` + `mul_eq_zero`. -/
theorem int_sumSq_eq_zero {a b : Int} (h : a * a + b * b = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨ha2, hb2⟩ :=
    E213.Meta.Int213.add_eq_zero_of_nonneg (int_sq_nonneg a) (int_sq_nonneg b) h
  refine ⟨?_, ?_⟩
  · rcases E213.Meta.Int213.mul_eq_zero ha2 with h0 | h0 <;> exact h0
  · rcases E213.Meta.Int213.mul_eq_zero hb2 with h0 | h0 <;> exact h0

/-- ★★★★ **`x² = −1` is unsolvable over ℤ in cleared-denominator
    form**: `a*a = −(b*b)` forces `a = b = 0`.  The order frame sees
    `a*a ≥ 0` and `−(b*b) ≤ 0`; they meet only at `0`.  This is the
    obstruction's *invisibility*: no choice of sign or magnitude on
    `(a, b)` produces a witness, unlike the difference-Lens (sign) or
    the ratio-Lens (remainder) whose witnesses live in the old data. -/
theorem sq_eq_neg_sq_imp {a b : Int} (h : a * a = -(b * b)) :
    a = 0 ∧ b = 0 := by
  apply int_sumSq_eq_zero
  rw [h]; exact add_left_neg (b * b)

/-- ★★★★★ **No rational squares to −1** (the archimedean rigidity
    witness).  For a rational `a/b` with `b ≠ 0`, the square
    `(a*a)/(b*b)` cannot equal `−1 = (−1)/1`:
    `ratioEqZ (a*a) (b*b) (−1) 1` would force `a*a = −(b*b)`, hence
    `b = 0` by `sq_eq_neg_sq_imp`, contradicting `b ≠ 0`.  So ℂ is a
    new axis over the sign, remainder, and order frames; the ∣-frames
    at `p ≡ 1 (mod 4)` see the question instead
    (`ModArith/QRNegOne.qr_neg_one`). -/
theorem no_rat_sqrt_neg_one {a : Int} {b : Nat} (hb : 0 < b)
    (h : ratioEqZ (a * a) (b * b) (-1) 1) : False := by
  -- ratioEqZ (a*a) (b*b) (-1) 1  :  (a*a) * ofNat 1 = (-1) * ofNat (b*b)
  have h1 : (a * a) * Int.ofNat 1 = (-1) * Int.ofNat (b * b) := h
  -- LHS = a*a (PURE Int213.mul_one, defeq on ofNat 1 = 1)
  have eL : (a * a) * Int.ofNat 1 = a * a := E213.Meta.Int213.mul_one (a * a)
  -- RHS = -(ofNat (b*b))
  have eR : (-1) * Int.ofNat (b * b) = -(Int.ofNat (b * b)) := by
    rw [E213.Meta.Int213.neg_mul, Int.one_mul]
  have hkey : a * a = -(Int.ofNat (b * b)) := by rw [← eL, h1, eR]
  -- ofNat (b*b) = ofNat b * ofNat b (defeq)
  have h3 : Int.ofNat (b * b) = Int.ofNat b * Int.ofNat b := rfl
  rw [h3] at hkey
  obtain ⟨_, hb0⟩ := sq_eq_neg_sq_imp hkey
  have hbz : b = 0 := Int.ofNat.inj hb0
  rw [hbz] at hb
  exact Nat.lt_irrefl 0 hb

end E213.Lib.Math.NumberSystems.CompletionDichotomy
