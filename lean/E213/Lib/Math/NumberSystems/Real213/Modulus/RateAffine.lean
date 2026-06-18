import E213.Lib.Math.NumberSystems.Real213.Modulus.RateProduct

/-!
# RateAffine — the affine action on modulus degree (translation & scaling)

`RateArithmetic` (matched sum: `W^{x+y}=W^x+W^y`, additive) and `RateProduct`
(matched product: loses a degree) gave the *binary* operations' action on the
convergent cross-determinant `W_i = a_{i+1}d_i − a_i d_{i+1}`.  This file gives the
*affine* (unary) action — `x ↦ x + m` and `x ↦ q·x` for an integer `m`, `q` — closing
the first-order **degree calculus**: how the field operations move the degree.

For `x = a/d`:

  * **Integer translation** `x + m` has convergents `(a + m·d)/d` — same denominator,
    and `W^{x+m}_i = W^x_i` **exactly** (`trans_cross_det`): the `m·d` terms cancel in
    the cross-determinant.  So **degree is translation-invariant** (same `W`, same `d`,
    same `DominatesS` — `trans_degree_invariant`).
  * **Integer scaling** `q·x` has convergents `(q·a)/d` — same denominator, and
    `W^{q·x}_i = q·W^x_i` (`scale_cross_det`).  So scaling multiplies the cross-determinant
    by the *constant* `q`: the **degree (growth class) is scale-invariant**, the per-layer
    budget paying a constant factor `q` (`scale_dominatesS`).

Assembled with the binary laws, the **degree calculus**: modulus degree is invariant
under the affine group (integer translation exactly, integer scaling up to the constant
`q`), additive under matched sum, and degrades by one under product.  Degree is a property
of the *pointing*, and the affine action is the part of the field action that preserves it
— translation/scaling are the `GL₂(ℤ)` lower-triangular (parabolic + diagonal) generators,
under which the rate is invariant; the off-diagonal (reciprocal) flips monotonicity and is
the genuinely degree-moving direction, handled with the binary product law.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.RateAffine

open E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification (DominatesS)
open E213.Lib.Math.NumberSystems.Real213.Modulus.DegreeCriterion (degree_le_of_increment)
open E213.Meta.Nat.RootFloor (rootFloor)

/-! ## §1 — integer translation: the cross-determinant is invariant -/

/-- The translated convergent numerator `a + m·d` (translation by the integer `m`). -/
def transNum (a d : Nat → Nat) (m : Nat) (i : Nat) : Nat := a i + m * d i

/-- ★★★ **Translation invariance of the cross-determinant.**  `x + m` has the *same*
    cross-determinant `W^x` over the *same* denominator `d`: the `m·d` contributions
    `m·d_{i+1}·d_i` and `m·d_i·d_{i+1}` cancel.  The affine shift moves the numerator but
    not the rate. -/
theorem trans_cross_det (a d Wx : Nat → Nat) (m : Nat)
    (hW : ∀ i, a (i + 1) * d i = a i * d (i + 1) + Wx i) (i : Nat) :
    transNum a d m (i + 1) * d i = transNum a d m i * d (i + 1) + Wx i := by
  show (a (i + 1) + m * d (i + 1)) * d i = (a i + m * d i) * d (i + 1) + Wx i
  rw [E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.add_mul, hW i]
  ring_nat

/-- ★★ **Degree is translation-invariant.**  Since `x + m` carries the same cross-determinant
    `W^x` and the same denominator `d`, it meets the degree-`s` increment criterion exactly
    when `x` does — same budget, same domination at every layer. -/
theorem trans_degree_invariant (a d Wx : Nat → Nat) (m s : Nat)
    (hbudget : ∀ i, rootFloor s i * Wx i + d i ≤ d (i + 1)) (i : Nat) :
    DominatesS Wx d (rootFloor s) i :=
  degree_le_of_increment s Wx d hbudget i

/-! ## §2 — integer scaling: the cross-determinant scales by the constant `q` -/

/-- The scaled convergent numerator `q·a` (scaling by the integer `q`). -/
def scaleNum (a : Nat → Nat) (q : Nat) (i : Nat) : Nat := q * a i

/-- ★★★ **Scaling acts on the cross-determinant by the constant `q`.**  `q·x` has
    cross-determinant `q·W^x` over the same denominator `d` — the rate is multiplied by the
    constant factor `q`, so the growth class (the degree) is unchanged. -/
theorem scale_cross_det (a d Wx : Nat → Nat) (q : Nat)
    (hW : ∀ i, a (i + 1) * d i = a i * d (i + 1) + Wx i) (i : Nat) :
    scaleNum a q (i + 1) * d i = scaleNum a q i * d (i + 1) + q * Wx i := by
  show q * a (i + 1) * d i = q * a i * d (i + 1) + q * Wx i
  have h : a (i + 1) * d i = a i * d (i + 1) + Wx i := hW i
  calc q * a (i + 1) * d i
      = q * (a (i + 1) * d i) := by ring_nat
    _ = q * (a i * d (i + 1) + Wx i) := by rw [h]
    _ = q * a i * d (i + 1) + q * Wx i := by ring_nat

/-- ★★ **Scaling preserves the degree growth class.**  `q·x` is degree-`s` dominated when
    the constant-`q`-scaled cross-determinant fits the increment; `q·W^x` has the same growth
    class in `i` as `W^x` (a constant multiple), so the degree is scale-invariant — the
    per-layer budget paying the constant factor `q`. -/
theorem scale_dominatesS (d Wx : Nat → Nat) (q s : Nat)
    (hbudget : ∀ i, rootFloor s i * (q * Wx i) + d i ≤ d (i + 1)) (i : Nat) :
    DominatesS (fun j => q * Wx j) d (rootFloor s) i :=
  degree_le_of_increment s (fun j => q * Wx j) d hbudget i

end E213.Lib.Math.NumberSystems.Real213.Modulus.RateAffine
