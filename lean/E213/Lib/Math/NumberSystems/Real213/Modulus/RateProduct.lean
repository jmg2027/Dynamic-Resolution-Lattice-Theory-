import E213.Lib.Math.NumberSystems.Real213.Modulus.RateArithmetic

/-!
# RateProduct — the modulus degree of a product, on a shared denominator

`RateArithmetic` showed degree is **not additive** under naive convergent arithmetic
(`sum_naive_not_dominatesS`) but **exactly additive on a shared denominator**
(`matched_sum_cross_det`: `W^{x+y} = W^x + W^y`).  It left the **product** open:
the naive product cross-determinant `prod_cross_det` carries the numerators, so a
product has no clean degree in general.

This file closes the product case in the same shared-denominator presentation, and
states the structural law it obeys.  For `x = a/d`, `y = b/d`, the product is
`xy = (a·b)/d²` — numerator `prodNumSh = a·b`, denominator `sqDen = d²`.  Its
cross-determinant is

  `W^{xy}_i = a_i·d_{i+1}·W^b_i + b_i·d_{i+1}·W^a_i + W^a_i·W^b_i`   (`prod_cross_det_sh`).

Unlike the matched **sum** (`W^{x+y} = W^x + W^y`, a clean add), the matched
**product** cross-determinant carries a `d_i·d_{i+1}` factor on the added
cross-determinants — *and the denominator is now `d²`*.  Under the honest normalisation
`a_i ≤ d_i`, `b_i ≤ d_i` (proper fractions — the fractional pointing, the only part the
cut sees), the carry is bounded:

  `W^{xy}_i ≤ d_i·d_{i+1}·(W^a_i + W^b_i) + W^a_i·W^b_i`   (`prod_cross_det_bound`).

> ★★★ **Product degree law** (`prod_dominatesS_of_budget`, `prod_graded_modulus`).
> With bounded factors, if the *joint* probe of the bounded cross-determinant fits the
> **squared-denominator** increment, `⌊i^{1/s}⌋·(d_i d_{i+1}(W^a+W^b) + W^a W^b) + d_i²
> ≤ d_{i+1}²`, then `x·y` is degree ≤ s through the `d²` presentation, with the
> constructed total modulus `N(m,k) = k^s + 1`.

**The structural finding — the product loses a degree.**  This is the genuine
counterpart to the matched-sum additivity.  The sum's cross-determinants *add* against
the *same* increment `d_{i+1} − d_i`; the product's add only after paying a
`d_i·d_{i+1}` carry, against the *squared* increment
`d_{i+1}² − d_i² = (d_{i+1}−d_i)(d_{i+1}+d_i)`.  So "each factor degree s" does **not**
give "product degree s": degree is a property of the *pointing*, and the `d²`
presentation of a product is a coarser pointing than the factors'.  (Matched sum: degree
preserved up to the combined cross-determinant; matched product: a `d_i d_{i+1}` carry —
the product is degree-wasteful where the sum is degree-clean.)

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.RateProduct

open E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
  (DominatesS dominatedS_graded_modulus)
open E213.Lib.Math.NumberSystems.Real213.Modulus.DegreeCriterion
  (dominatesS_of_scheduled_increment)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (rcut)
open E213.Meta.Nat.RootFloor (rootFloor rootFloor_mono)

/-! ## §1 — the shared-denominator product presentation -/

/-- Product convergent numerator on a shared denominator: `a·b` over `d²`. -/
def prodNumSh (a b : Nat → Nat) (i : Nat) : Nat := a i * b i

/-- The squared denominator `d²` carrying the product convergent. -/
def sqDen (d : Nat → Nat) (i : Nat) : Nat := d i * d i

/-- The product cross-determinant on the shared denominator, abbreviated. -/
def prodW (a b d Wa Wb : Nat → Nat) (i : Nat) : Nat :=
  a i * d (i + 1) * Wb i + b i * d (i + 1) * Wa i + Wa i * Wb i

/-- The bounded envelope `d_i·d_{i+1}·(Wa+Wb) + Wa·Wb`. -/
def prodWbound (d Wa Wb : Nat → Nat) (i : Nat) : Nat :=
  d i * d (i + 1) * (Wa i + Wb i) + Wa i * Wb i

/-! ## §2 — the cross-determinant of the matched product -/

/-- ★★★ **Cross-determinant of the shared-denominator product.**
    `W^{xy}_i = a_i·d_{i+1}·W^b_i + b_i·d_{i+1}·W^a_i + W^a_i·W^b_i` — the matched
    product's cross-determinant, the specialisation of `prod_cross_det` to `e = d`.
    Unlike the matched sum (`matched_sum_cross_det`, a clean `W^a + W^b`), it carries the
    numerators. -/
theorem prod_cross_det_sh (a b d Wa Wb : Nat → Nat)
    (hWa : ∀ i, a (i + 1) * d i = a i * d (i + 1) + Wa i)
    (hWb : ∀ i, b (i + 1) * d i = b i * d (i + 1) + Wb i) (i : Nat) :
    prodNumSh a b (i + 1) * sqDen d i
      = prodNumSh a b i * sqDen d (i + 1) + prodW a b d Wa Wb i := by
  show (a (i + 1) * b (i + 1)) * (d i * d i)
      = (a i * b i) * (d (i + 1) * d (i + 1))
        + (a i * d (i + 1) * Wb i + b i * d (i + 1) * Wa i + Wa i * Wb i)
  have key : (a (i + 1) * b (i + 1)) * (d i * d i)
      = (a (i + 1) * d i) * (b (i + 1) * d i) := by ring_nat
  rw [key, hWa i, hWb i]; ring_nat

/-! ## §3 — bounded factors collapse the carry -/

/-- ★★ **Bounded numerators bound the carry.**  With `a_i ≤ d_i`, `b_i ≤ d_i` (proper
    fractions), the product cross-determinant is dominated by
    `d_i·d_{i+1}·(W^a + W^b) + W^a·W^b` — the cross-determinants add, but only after a
    `d_i·d_{i+1}` carry. -/
theorem prod_cross_det_bound (a b d Wa Wb : Nat → Nat)
    (hab : ∀ i, a i ≤ d i) (hbd : ∀ i, b i ≤ d i) (i : Nat) :
    prodW a b d Wa Wb i ≤ prodWbound d Wa Wb i := by
  show a i * d (i + 1) * Wb i + b i * d (i + 1) * Wa i + Wa i * Wb i
      ≤ d i * d (i + 1) * (Wa i + Wb i) + Wa i * Wb i
  apply Nat.add_le_add_right
  have h1 : a i * d (i + 1) * Wb i ≤ d i * d (i + 1) * Wb i :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hab i))
  have h2 : b i * d (i + 1) * Wa i ≤ d i * d (i + 1) * Wa i :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hbd i))
  have hsum : d i * d (i + 1) * Wb i + d i * d (i + 1) * Wa i
      = d i * d (i + 1) * (Wa i + Wb i) := by ring_nat
  calc a i * d (i + 1) * Wb i + b i * d (i + 1) * Wa i
      ≤ d i * d (i + 1) * Wb i + d i * d (i + 1) * Wa i := Nat.add_le_add h1 h2
    _ = d i * d (i + 1) * (Wa i + Wb i) := hsum

/-! ## §4 — the product degree law -/

/-- ★★★ **Product degree law (per layer).**  With bounded factors, if the degree-`s` probe
    of the bounded cross-determinant fits the squared-denominator increment at layer `i`
    (`⌊i^{1/s}⌋·(d_i d_{i+1}(W^a+W^b) + W^a W^b) + d_i² ≤ d_{i+1}²`), layer `i` of the
    product `(a·b)/d²` is degree-`s` dominated. -/
theorem prod_dominatesS_of_budget (a b d Wa Wb : Nat → Nat)
    (hab : ∀ i, a i ≤ d i) (hbd : ∀ i, b i ≤ d i) (s i : Nat)
    (hbudget : rootFloor s i * prodWbound d Wa Wb i + sqDen d i ≤ sqDen d (i + 1)) :
    DominatesS (prodW a b d Wa Wb) (sqDen d) (rootFloor s) i := by
  apply dominatesS_of_scheduled_increment (prodW a b d Wa Wb) (sqDen d) (rootFloor s) i
    (rootFloor_mono s (Nat.le_succ i))
  refine Nat.le_trans (Nat.add_le_add_right ?_ (sqDen d i)) hbudget
  exact Nat.mul_le_mul_left (rootFloor s i) (prod_cross_det_bound a b d Wa Wb hab hbd i)

/-- ★★★ **Product graded completion.**  A monotone matched-product presentation
    `(a·b)/d²` whose every layer meets the degree-`s` squared-increment budget has a total
    ∅-axiom modulus `N(m,k) = k^s + 1`.  The product is *completable* through its `d²`
    pointing — at the degree the squared-increment budget allows, one step coarser than the
    factors (the `d_i d_{i+1}` carry of `prod_cross_det_bound`). -/
theorem prod_graded_modulus (a b d Wa Wb : Nat → Nat) (s : Nat) (hs : 1 ≤ s)
    (hWa : ∀ i, a (i + 1) * d i = a i * d (i + 1) + Wa i)
    (hWb : ∀ i, b (i + 1) * d i = b i * d (i + 1) + Wb i)
    (hab : ∀ i, a i ≤ d i) (hbd : ∀ i, b i ≤ d i)
    (hsq : ∀ i, 1 ≤ sqDen d i)
    (hbudget : ∀ i, 1 ≤ i →
        rootFloor s i * prodWbound d Wa Wb i + sqDen d i ≤ sqDen d (i + 1))
    (hmono : ∀ N i, N ≤ i → prodNumSh a b N * sqDen d i ≤ prodNumSh a b i * sqDen d N)
    (hmonoS : ∀ i, prodNumSh a b i * sqDen d (i + 1) < prodNumSh a b (i + 1) * sqDen d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (prodNumSh a b) (sqDen d) i m k = rcut (prodNumSh a b) (sqDen d) j m k :=
  dominatedS_graded_modulus s hs (prodW a b d Wa Wb) hsq
    (prod_cross_det_sh a b d Wa Wb hWa hWb)
    (fun i hi => prod_dominatesS_of_budget a b d Wa Wb hab hbd s i (hbudget i hi))
    hmono hmonoS m k hk

end E213.Lib.Math.NumberSystems.Real213.Modulus.RateProduct
