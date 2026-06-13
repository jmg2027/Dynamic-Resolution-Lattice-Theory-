import E213.Lib.Math.NumberSystems.Real213.DegreeCriterion

/-!
# RateArithmetic — the cross-determinant under sum/product, and why degree is not additive

The convergents of `x + y` and `x · y` from convergents of `x = a/d`, `y = b/e`:

    sum:      c_i = a_i·e_i + b_i·d_i,   f_i = d_i·e_i
    product:  c_i = a_i·b_i,             f_i = d_i·e_i

Their cross-determinants factor cleanly through the summands' (`sum_cross_det`,
`prod_cross_det`):

    W^{x+y}_i = W^x_i·e_i e_{i+1} + W^y_i·d_i d_{i+1}
    W^{xy}_i  = a_i d_{i+1}·W^y_i + b_i e_{i+1}·W^x_i + W^x_i·W^y_i

**The honest finding** (`sum_naive_not_dominatesS`): the sum's cross-determinant
carries the *other* presentation's denominator (`e_i e_{i+1}`).  So when `y`'s
denominators outgrow `x`'s, `W^{x+y}` overtakes the naive denominator
`f_{i+1} = d_{i+1}e_{i+1}` — and the naive sum is **not dominated at any degree**,
even when both summands are degree 1 (e.g. `e + e` via common denominators
`(i!)²` is rate-free, though `2e` is trivially degree 1 by scaling).  Modulus
degree is **not a function of the real** under `+`/`·`: it is a property of the
chosen pointing, and naive convergent arithmetic is degree-wasteful.  Closure of
the completable class holds only with a *good* presentation, not the naive one
(`theory/math/analysis/holonomic_modulus.md`: presentation-dependence).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.RateArithmetic

open E213.Lib.Math.NumberSystems.Real213.RateStratification (DominatesS)
open E213.Lib.Math.NumberSystems.Real213.DegreeCriterion (not_dominatesS_of_overtake)
open E213.Meta.Nat.RootFloor (rootFloor rootFloor_pos)

/-! ## §1 — the sum/product convergents and their cross-determinants -/

/-- The sum convergent numerator: `(a/d + b/e)`'s numerator over the common
    denominator `d·e`. -/
def sumNum (a d b e : Nat → Nat) (i : Nat) : Nat := a i * e i + b i * d i
/-- The common denominator `d·e`, shared by the sum and product presentations. -/
def comDen (d e : Nat → Nat) (i : Nat) : Nat := d i * e i
/-- The product convergent numerator `a·b`. -/
def prodNum (a b : Nat → Nat) (i : Nat) : Nat := a i * b i

/-- ★★★ **Cross-determinant of the sum.**  `W^{x+y}_i = W^x_i·e_i e_{i+1} +
    W^y_i·d_i d_{i+1}` — the sum's cross-determinant carries *each summand's*
    cross-determinant weighted by the *other* presentation's adjacent
    denominators. -/
theorem sum_cross_det (a d b e Wa Wb : Nat → Nat)
    (hWa : ∀ i, a (i+1) * d i = a i * d (i+1) + Wa i)
    (hWb : ∀ i, b (i+1) * e i = b i * e (i+1) + Wb i) (i : Nat) :
    sumNum a d b e (i+1) * comDen d e i
      = sumNum a d b e i * comDen d e (i+1)
        + (Wa i * (e i * e (i+1)) + Wb i * (d i * d (i+1))) := by
  show (a (i+1) * e (i+1) + b (i+1) * d (i+1)) * (d i * e i)
      = (a i * e i + b i * d i) * (d (i+1) * e (i+1))
        + (Wa i * (e i * e (i+1)) + Wb i * (d i * d (i+1)))
  have key : (a (i+1) * e (i+1) + b (i+1) * d (i+1)) * (d i * e i)
      = (a (i+1) * d i) * (e (i+1) * e i) + (b (i+1) * e i) * (d (i+1) * d i) := by
    ring_nat
  rw [key, hWa i, hWb i]; ring_nat

/-- ★★★ **Cross-determinant of the product.**  `W^{xy}_i = a_i d_{i+1}·W^y_i +
    b_i e_{i+1}·W^x_i + W^x_i·W^y_i`. -/
theorem prod_cross_det (a d b e Wa Wb : Nat → Nat)
    (hWa : ∀ i, a (i+1) * d i = a i * d (i+1) + Wa i)
    (hWb : ∀ i, b (i+1) * e i = b i * e (i+1) + Wb i) (i : Nat) :
    prodNum a b (i+1) * comDen d e i
      = prodNum a b i * comDen d e (i+1)
        + (a i * d (i+1) * Wb i + b i * e (i+1) * Wa i + Wa i * Wb i) := by
  show (a (i+1) * b (i+1)) * (d i * e i)
      = (a i * b i) * (d (i+1) * e (i+1))
        + (a i * d (i+1) * Wb i + b i * e (i+1) * Wa i + Wa i * Wb i)
  have key : (a (i+1) * b (i+1)) * (d i * e i)
      = (a (i+1) * d i) * (b (i+1) * e i) := by ring_nat
  rw [key, hWa i, hWb i]; ring_nat

/-! ## §2 — degree is not additive: naive convergent arithmetic is wasteful -/

/-- ★★ **The naive sum breaks at any degree when denominators are mismatched.**
    If `y`'s denominator outgrows `x`'s at layer `i` (`d_{i+1} < e_i`, with
    `e_{i+1} ≥ 1`) and `x`'s cross-determinant is nonzero (`Wa_i ≥ 1`), then the
    sum's cross-determinant `W^{x+y}_i = Wa_i·e_i e_{i+1} + Wb_i·d_i d_{i+1}`
    overtakes the naive denominator `f_{i+1} = d_{i+1}e_{i+1}` — so for *every*
    degree `s` the naive sum is not dominated at layer `i ≥ 1`.  Both summands can
    be degree 1; the naive common-denominator addition still destroys the rate,
    because it picks up the other denominator quadratically.  Degree is a property
    of the pointing, not of `x+y`. -/
theorem sum_naive_not_dominatesS (d e Wa Wb : Nat → Nat) (s i : Nat)
    (hi : 1 ≤ i) (hWa1 : 1 ≤ Wa i) (hepos : 1 ≤ e (i+1)) (hgrow : d (i+1) < e i) :
    ¬ DominatesS (fun j => Wa j * (e j * e (j+1)) + Wb j * (d j * d (j+1)))
        (comDen d e) (rootFloor s) i := by
  apply not_dominatesS_of_overtake
  show d (i+1) * e (i+1)
      < rootFloor s i * (Wa i * (e i * e (i+1)) + Wb i * (d i * d (i+1)))
  have hrs : 1 ≤ rootFloor s i := rootFloor_pos s i hi
  have hstrict : d (i+1) * e (i+1) < e i * e (i+1) := by
    have h1 : d (i+1) * e (i+1) + e (i+1) ≤ e i * e (i+1) := by
      have h := Nat.mul_le_mul_right (e (i+1)) hgrow
      rwa [Nat.succ_mul] at h
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hepos) h1
  calc d (i+1) * e (i+1)
      < e i * e (i+1) := hstrict
    _ ≤ Wa i * (e i * e (i+1)) := Nat.le_mul_of_pos_left _ hWa1
    _ ≤ Wa i * (e i * e (i+1)) + Wb i * (d i * d (i+1)) := Nat.le_add_right _ _
    _ ≤ rootFloor s i * (Wa i * (e i * e (i+1)) + Wb i * (d i * d (i+1))) :=
        Nat.le_mul_of_pos_left _ hrs

end E213.Lib.Math.NumberSystems.Real213.RateArithmetic
