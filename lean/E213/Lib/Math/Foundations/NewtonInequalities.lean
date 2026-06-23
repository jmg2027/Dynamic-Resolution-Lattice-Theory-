import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul
import E213.Meta.Int213.PolyIntMTactic

/-!
# Newton's inequalities for 3-variable elementary symmetric functions (∅-axiom)

For `a b c : Int` with elementary symmetric functions
  `e1 = a+b+c`, `e2 = ab+bc+ca`, `e3 = abc`,

* ★★★ **Newton #1**: `e1² ≥ 3·e2`, i.e. `(a+b+c)² ≥ 3(ab+bc+ca)`.
    SOS: `2·(e1² − 3e2) = (a−b)² + (b−c)² + (c−a)² ≥ 0`.
* ★★★ **Newton #2**: `e2² ≥ 3·e1·e3`, i.e. `(ab+bc+ca)² ≥ 3(a+b+c)·abc`.
    SOS: `2·(e2² − 3e1e3) = (ab−bc)² + (bc−ca)² + (ca−ab)² ≥ 0`.

Neither requires any ordering hypothesis — pure sum-of-squares.

Proof skeleton (copied from `SchurInequality.lean` / `NesbittInequality.lean`):
1. a `ring_intZ` identity rewriting `2·(LHS−RHS)` into a manifest sum of squares;
2. each square `0 ≤ x*x` via `int_sq_nonneg`;
3. `add_nonneg` to sum them, giving `0 ≤ 2·(LHS−RHS)`;
4. **halving** `0 ≤ 2·t → 0 ≤ t` via `le_of_mul_le_mul_right_pos` (PURE,
   already in `Meta.Int213.OrderMul`), then `le_of_sub_nonneg` to conclude.

All PURE: order facts route through the `E213.Meta.Int213` corpus.
-/

namespace E213.Lib.Math.Foundations.NewtonInequalities

open E213.Meta.Int213 (int_sq_nonneg add_nonneg)

/-- **Halving** (ℤ): `0 ≤ 2·t ⟹ 0 ≤ t`.  PURE, no division.
    From `0·2 ≤ t·2` and `0 < 2`, cancel the positive factor `2`
    (`le_of_mul_le_mul_right_pos`). -/
theorem nonneg_of_two_mul_nonneg {t : Int} (h : (0 : Int) ≤ 2 * t) : (0 : Int) ≤ t := by
  apply E213.Meta.Int213.OrderMul.le_of_mul_le_mul_right_pos (c := 2) (hc := by decide)
  -- goal: 0 * 2 ≤ t * 2
  rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.mul_comm t 2]
  exact h

/-! ## Newton #1 -/

/-- ★★★ **Newton's inequality #1** (ℤ): `(a+b+c)² ≥ 3(ab+bc+ca)`, i.e. `e1² ≥ 3·e2`.
    SOS: `2·(e1²−3e2) = (a−b)² + (b−c)² + (c−a)²`.  No ordering hypothesis. -/
theorem newton1 (a b c : Int) :
    3*(a*b + b*c + c*a) ≤ (a+b+c)*(a+b+c) := by
  -- doubled SOS identity
  have hid : 2*((a+b+c)*(a+b+c) - 3*(a*b + b*c + c*a))
      = (a-b)*(a-b) + ((b-c)*(b-c) + (c-a)*(c-a)) := by ring_intZ
  have hsq : (0 : Int) ≤ (a-b)*(a-b) + ((b-c)*(b-c) + (c-a)*(c-a)) :=
    add_nonneg (int_sq_nonneg (a-b))
      (add_nonneg (int_sq_nonneg (b-c)) (int_sq_nonneg (c-a)))
  have h2 : (0 : Int) ≤ 2*((a+b+c)*(a+b+c) - 3*(a*b + b*c + c*a)) := by
    rw [hid]; exact hsq
  have hdiff : (0 : Int) ≤ (a+b+c)*(a+b+c) - 3*(a*b + b*c + c*a) :=
    nonneg_of_two_mul_nonneg h2
  exact E213.Meta.Int213.Order.le_of_sub_nonneg
    (E213.Meta.Int213.Order.nonneg_of_le_zero hdiff)

/-- ★★★ **Newton #1, doubled SOS form** (ℤ): `2·(e1²−3e2) = Σ (a−b)²`.
    Manifestly nonneg; the un-halved companion to `newton1`. -/
theorem newton1_doubled (a b c : Int) :
    2*((a+b+c)*(a+b+c) - 3*(a*b + b*c + c*a))
      = (a-b)*(a-b) + ((b-c)*(b-c) + (c-a)*(c-a)) := by ring_intZ

/-! ## Newton #2 -/

/-- ★★★ **Newton's inequality #2** (ℤ): `(ab+bc+ca)² ≥ 3(a+b+c)·abc`, i.e. `e2² ≥ 3·e1·e3`.
    SOS: `2·(e2²−3e1e3) = (ab−bc)² + (bc−ca)² + (ca−ab)²`.  No ordering hypothesis. -/
theorem newton2 (a b c : Int) :
    3*(a+b+c)*(a*b*c) ≤ (a*b + b*c + c*a)*(a*b + b*c + c*a) := by
  -- doubled SOS identity
  have hid : 2*((a*b + b*c + c*a)*(a*b + b*c + c*a) - 3*(a+b+c)*(a*b*c))
      = (a*b - b*c)*(a*b - b*c)
          + ((b*c - c*a)*(b*c - c*a) + (c*a - a*b)*(c*a - a*b)) := by ring_intZ
  have hsq : (0 : Int) ≤ (a*b - b*c)*(a*b - b*c)
          + ((b*c - c*a)*(b*c - c*a) + (c*a - a*b)*(c*a - a*b)) :=
    add_nonneg (int_sq_nonneg (a*b - b*c))
      (add_nonneg (int_sq_nonneg (b*c - c*a)) (int_sq_nonneg (c*a - a*b)))
  have h2 : (0 : Int) ≤
      2*((a*b + b*c + c*a)*(a*b + b*c + c*a) - 3*(a+b+c)*(a*b*c)) := by
    rw [hid]; exact hsq
  have hdiff : (0 : Int) ≤
      (a*b + b*c + c*a)*(a*b + b*c + c*a) - 3*(a+b+c)*(a*b*c) :=
    nonneg_of_two_mul_nonneg h2
  exact E213.Meta.Int213.Order.le_of_sub_nonneg
    (E213.Meta.Int213.Order.nonneg_of_le_zero hdiff)

/-- ★★★ **Newton #2, doubled SOS form** (ℤ): `2·(e2²−3e1e3) = Σ (ab−bc)²`. -/
theorem newton2_doubled (a b c : Int) :
    2*((a*b + b*c + c*a)*(a*b + b*c + c*a) - 3*(a+b+c)*(a*b*c))
      = (a*b - b*c)*(a*b - b*c)
          + ((b*c - c*a)*(b*c - c*a) + (c*a - a*b)*(c*a - a*b)) := by ring_intZ

/-! ## Newton's identities — the power-sum ↔ elementary-symmetric character bridge

The two readings of one 3-element spectrum `{a,b,c}`:

* the **multiplicative** (×↦·) reading — the elementary symmetric `e1 = a+b+c`,
  `e2 = ab+bc+ca`, `e3 = abc` (the coefficients of `∏(t+xⱼ)`, the universal
  `det`/char-poly; `e1 = tr`, `e2 = det` of the 2×2 case in `Mat2Spectrum`);
* the **additive** (×↦+) reading — the power sums `p_k = aᵏ+bᵏ+cᵏ` (the
  `tr(Mᵏ)` trace-powers).

**Newton's identities** are the exact bridge between the two characters — each
`p_k` written through the `eᵢ`.  These are genuine symmetric-function theorems
(`SchurInequality.lean`/`NewtonInequalities` neighbours), the degree-by-degree
companion to the closed `newton1`/`newton2` log-concavity inequalities.  Both
∅-axiom: a single `ring_intZ` polynomial identity. -/

/-- ★★ **Newton's identity, degree 2** (ℤ): `p₂ = e₁·p₁ − 2·e₂`, i.e.
    `a²+b²+c² = (a+b+c)² − 2(ab+bc+ca)`.  The power-sum ↔ elementary bridge at
    degree 2 (`p₁ = e₁` is the degree-1 identity, definitional). -/
theorem newton_id_p2 (a b c : Int) :
    a*a + b*b + c*c
      = (a+b+c)*(a+b+c) - 2*(a*b + b*c + c*a) := by ring_intZ

/-- ★★ **Newton's identity, degree 3** (ℤ): `p₃ = e₁·p₂ − e₂·p₁ + 3·e₃`, i.e.
    `a³+b³+c³ = (a+b+c)(a²+b²+c²) − (ab+bc+ca)(a+b+c) + 3abc`.  The degree-3
    `×↦+ ↔ ×↦·` character bridge; reduces to the classical `a³+b³+c³−3abc
    = (a+b+c)(a²+b²+c²−ab−bc−ca)` once `e₁p₂−e₂p₁` collapses to `p₃−3e₃`. -/
theorem newton_id_p3 (a b c : Int) :
    a*a*a + b*b*b + c*c*c
      = (a+b+c)*(a*a + b*b + c*c)
          - (a*b + b*c + c*a)*(a+b+c) + 3*(a*b*c) := by ring_intZ

/-- ★★ **Newton's identity, degree 4** (ℤ): `p₄ = e₁·p₃ − e₂·p₂ + e₃·p₁`, i.e.
    `a⁴+b⁴+c⁴ = (a+b+c)(a³+b³+c³) − (ab+bc+ca)(a²+b²+c²) + abc(a+b+c)`.  The
    `k > n` Newton recurrence (3 variables, so `e₄ = 0` — no standalone `k·e_k`
    term); the degree-4 `×↦+ ↔ ×↦·` bridge.  This is also the `n = 2` case of the
    Newton–Girard *recurrence* `p_{k} = e₁p_{k-1} − e₂p_{k-2} + e₃p_{k-3}`. -/
theorem newton_id_p4 (a b c : Int) :
    a*a*a*a + b*b*b*b + c*c*c*c
      = (a+b+c)*(a*a*a + b*b*b + c*c*c)
          - (a*b + b*c + c*a)*(a*a + b*b + c*c)
          + (a*b*c)*(a+b+c) := by ring_intZ

/-! ## Maclaurin remark

The two Newton inequalities `e1² ≥ 3·e2` and `e2² ≥ 3·e1·e3` are exactly the
log-concavity (Newton) relations for the elementary symmetric functions in
three variables.  Writing the normalized means `p_k = e_k / C(3,k)`
(`p_0 = 1`, `p_1 = e1/3`, `p_2 = e2/3`, `p_3 = e3`), Newton's inequalities are
`p_k² ≥ p_{k-1}·p_{k+1}`:

* `k = 1`: `p_1² ≥ p_0·p_2`  ⟺  `(e1/3)² ≥ e2/3`  ⟺  `e1² ≥ 3·e2`  (= `newton1`).
* `k = 2`: `p_2² ≥ p_1·p_3`  ⟺  `(e2/3)² ≥ (e1/3)·e3`  ⟺  `e2² ≥ 3·e1·e3` (= `newton2`).

These are the clean `Int`-polynomial pieces; the Maclaurin mean chain
`p_1 ≥ √p_2 ≥ ∛p_3` introduces real roots and is *not* stated here (kept
entirely `Int`-polynomial per the ∅-axiom contract).
-/

/-! ### Concrete smokes (closed terms, `decide`).  Equality at `a=b=c`. -/

-- Newton #1
example : 3*((1:Int)*1 + 1*1 + 1*1) ≤ (1+1+1)*(1+1+1) := by decide   -- equality at a=b=c
example : 3*((1:Int)*2 + 2*3 + 3*1) ≤ (1+2+3)*(1+2+3) := by decide
example : 3*((2:Int)*2 + 2*2 + 2*2) ≤ (2+2+2)*(2+2+2) := by decide   -- equality
example : 3*((-1:Int)*2 + 2*5 + 5*(-1)) ≤ ((-1)+2+5)*((-1)+2+5) := by decide

-- Newton #1 doubled identity, numeric instance
example : 2*(((1:Int)+2+3)*(1+2+3) - 3*(1*2 + 2*3 + 3*1))
    = (1-2)*(1-2) + ((2-3)*(2-3) + (3-1)*(3-1)) := by decide

-- Newton #2
example : 3*((1:Int)+1+1)*(1*1*1) ≤ (1*1 + 1*1 + 1*1)*(1*1 + 1*1 + 1*1) := by decide  -- equality
example : 3*((1:Int)+2+3)*(1*2*3) ≤ (1*2 + 2*3 + 3*1)*(1*2 + 2*3 + 3*1) := by decide
example : 3*((2:Int)+2+2)*(2*2*2) ≤ (2*2 + 2*2 + 2*2)*(2*2 + 2*2 + 2*2) := by decide  -- equality
example : 3*((-1:Int)+2+5)*((-1)*2*5) ≤ ((-1)*2 + 2*5 + 5*(-1))*((-1)*2 + 2*5 + 5*(-1)) := by decide

-- Newton #2 doubled identity, numeric instance
example : 2*(((1:Int)*2 + 2*3 + 3*1)*(1*2 + 2*3 + 3*1) - 3*(1+2+3)*(1*2*3))
    = (1*2 - 2*3)*(1*2 - 2*3)
        + ((2*3 - 3*1)*(2*3 - 3*1) + (3*1 - 1*2)*(3*1 - 1*2)) := by decide

end E213.Lib.Math.Foundations.NewtonInequalities
