import E213.Lib.Math.NumberSystems.Real213.Modulus.RateProduct
import E213.Meta.Nat.Iterate213

/-!
# RatePower — the power cross-determinant factors through a symmetric polynomial

The degree calculus (`RateArithmetic` sum, `RateProduct` product, `RateAffine` affine +
reciprocal) gives the field operations' action on the convergent cross-determinant `W`.
This file handles **powers** `xⁿ`, the iterate of the product.

For `x = a/d`, `xⁿ = aⁿ/dⁿ`.  Writing the two adjacent convergent-products
`p_i := a_{i+1}·d_i` and `q_i := a_i·d_{i+1}` (so `hW`: `p_i = q_i + W_i`, `p_i ≥ q_i`), the
power cross-determinant is `p_iⁿ − q_iⁿ`, which factors by `pⁿ − qⁿ = (p−q)·h_{n−1}(p,q)`:

> ★★★ `pow_cross_det` : `W^{xⁿ}_i = W_i · geomH p_i q_i n`,

where `geomH p q n = Σ_{j=0}^{n−1} p^{n−1−j} q^j` is the **complete homogeneous symmetric
polynomial** `h_{n−1}(p,q)` of the two convergent-products.  This recovers `n=1`
(`W·1 = W`) and the product `n=2` (`W·(p+q)`).  The driver is the additive telescoping
identity `q^n + W·geomH (q+W) q n = (q+W)^n` (`pow_factor`, ∅-axiom over `Nat`, no
subtraction).

So the entire degree calculus is *one* symmetric-function statement: the cross-determinant of
`xⁿ` is `W` times the degree-`(n−1)` complete homogeneous symmetric polynomial of the two
adjacent convergent-products — the power's rate is carried by `W` (the unit cross-determinant)
scaled by a symmetric form that grows with `n` and with the convergent size, which is *why*
higher powers cost more degree (the `geomH` factor, bounded by `n·p^{n−1}` via `geomH_le`).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.RatePower

/-! ## §1 — the symmetric polynomial and the telescoping identity -/

/-- The complete homogeneous symmetric polynomial `h_{n−1}(p,q) = Σ_{j=0}^{n−1} p^{n−1−j} q^j`
    (`geomH p q 0 = 0`, `geomH p q (n+1) = pⁿ + q·geomH p q n`). -/
def geomH (p q : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => p ^ n + q * geomH p q n

/-- ★★★ **Telescoping identity** `pⁿ − qⁿ = (p − q)·h_{n−1}`, additive form (`p = q + W`):
    `qⁿ + W·geomH (q+W) q n = (q+W)ⁿ`.  ∅-axiom over `Nat`, no subtraction. -/
theorem pow_factor (q W : Nat) : ∀ n, q ^ n + W * geomH (q + W) q n = (q + W) ^ n
  | 0 => by
    show q ^ 0 + W * 0 = (q + W) ^ 0
    rw [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.pow_zero]
  | n + 1 => by
    have ih : q ^ n + W * geomH (q + W) q n = (q + W) ^ n := pow_factor q W n
    show q ^ (n + 1) + W * ((q + W) ^ n + q * geomH (q + W) q n) = (q + W) ^ (n + 1)
    rw [Nat.pow_succ q n]
    have key : q ^ n * q + W * ((q + W) ^ n + q * geomH (q + W) q n)
             = q * (q ^ n + W * geomH (q + W) q n) + W * (q + W) ^ n := by ring_nat
    rw [key, ih, ← E213.Tactic.NatHelper.add_mul, Nat.mul_comm (q + W) ((q + W) ^ n),
        ← Nat.pow_succ]

/-! ## §2 — the power convergents and their cross-determinant -/

/-- The power convergent numerator `aⁿ`. -/
def powNum (a : Nat → Nat) (n : Nat) (i : Nat) : Nat := (a i) ^ n
/-- The power convergent denominator `dⁿ`. -/
def powDen (d : Nat → Nat) (n : Nat) (i : Nat) : Nat := (d i) ^ n
/-- The power cross-determinant `W · h_{n−1}(p,q)`. -/
def powW (a d W : Nat → Nat) (n : Nat) (i : Nat) : Nat :=
  W i * geomH (a (i + 1) * d i) (a i * d (i + 1)) n

/-- ★★★ **The power cross-determinant factors as `W · h_{n−1}(p,q)`.**  `W^{xⁿ}_i =
    W_i · Σ_{j<n} (a_{i+1}d_i)^{n−1−j}(a_i d_{i+1})^j` — `W` (the unit cross-determinant of
    `x`) times the complete homogeneous symmetric polynomial of the two adjacent
    convergent-products.  The whole degree calculus, for powers, is this one symmetric form. -/
theorem pow_cross_det (a d W : Nat → Nat) (n : Nat)
    (hW : ∀ i, a (i + 1) * d i = a i * d (i + 1) + W i) (i : Nat) :
    powNum a n (i + 1) * powDen d n i
      = powNum a n i * powDen d n (i + 1) + powW a d W n i := by
  show (a (i + 1)) ^ n * (d i) ^ n
      = (a i) ^ n * (d (i + 1)) ^ n
        + W i * geomH (a (i + 1) * d i) (a i * d (i + 1)) n
  rw [← E213.Meta.Nat.Iterate213.mul_pow_pure, ← E213.Meta.Nat.Iterate213.mul_pow_pure, hW i]
  exact (pow_factor (a i * d (i + 1)) (W i) n).symm

/-! ## §3 — the symmetric polynomial's growth bound (the degree cost) -/

/-- `h_{n}(p,q) ≤ (n+1)·pⁿ` when `q ≤ p`: each of the `n+1` terms is `≤ pⁿ`.  So the power
    cross-determinant `W·geomH` grows like `n·pⁿ⁻¹` — the symmetric factor is *why* higher
    powers cost more modulus degree. -/
theorem geomH_le (p q : Nat) (h : q ≤ p) : ∀ n, geomH p q (n + 1) ≤ (n + 1) * p ^ n := by
  intro n
  induction n with
  | zero =>
    have hz : p ^ 0 + q * 0 = 1 * p ^ 0 := by rw [Nat.mul_zero, Nat.add_zero, Nat.one_mul]
    exact Nat.le_of_eq hz
  | succ n ih =>
    show p ^ (n + 1) + q * geomH p q (n + 1) ≤ (n + 1 + 1) * p ^ (n + 1)
    have hstep : p ^ (n + 1) + q * geomH p q (n + 1) ≤ p ^ (n + 1) + (n + 1) * p ^ (n + 1) := by
      apply Nat.add_le_add_left
      calc q * geomH p q (n + 1)
          ≤ p * ((n + 1) * p ^ n) := Nat.mul_le_mul h ih
        _ = (n + 1) * (p ^ n * p) := by ring_nat
        _ = (n + 1) * p ^ (n + 1) := by rw [← Nat.pow_succ]
    refine Nat.le_trans hstep (Nat.le_of_eq ?_)
    show p ^ (n + 1) + (n + 1) * p ^ (n + 1) = (n + 1 + 1) * p ^ (n + 1)
    ring_nat

/-- ★★ **The power cross-determinant grows like `n·pⁿ⁻¹`.**  With `q ≤ p` (cross-determinant
    positivity, from `hW`), `W^{xⁿ⁺¹}_i ≤ W_i·(n+1)·p_iⁿ` where `p_i = a_{i+1}d_i`.  Since
    `p_i ≤ d_{i+1}d_i` (proper factors `a ≤ d`), the carry lives at denominator-degree
    `2n` while the `dⁿ⁺¹` increment supplies only degree `n` — so the power loses *between*
    `n` and `2n` degrees (exactly `n` only on a denominator-flat / degree-1-saturated
    pointing, strictly more off it).  This is the honest power law completing the calculus. -/
theorem pow_cross_det_bound (a d W : Nat → Nat) (n : Nat)
    (hW : ∀ i, a (i + 1) * d i = a i * d (i + 1) + W i) (i : Nat) :
    powW a d W (n + 1) i ≤ W i * ((n + 1) * (a (i + 1) * d i) ^ n) := by
  show W i * geomH (a (i + 1) * d i) (a i * d (i + 1)) (n + 1)
      ≤ W i * ((n + 1) * (a (i + 1) * d i) ^ n)
  apply Nat.mul_le_mul_left
  apply geomH_le
  rw [hW i]
  exact Nat.le_add_right _ _

end E213.Lib.Math.NumberSystems.Real213.Modulus.RatePower
