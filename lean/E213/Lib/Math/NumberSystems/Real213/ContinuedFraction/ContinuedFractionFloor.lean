import E213.Meta.Int213
import E213.Meta.Algebra213.Core

/-!
# ContinuedFractionFloor — every real's continued fraction sits on the det-one floor

`Cauchy/DepthFloorDetOne` and `Real213/CrossDet/CrossDetConstDenom` put the det-one floor
(cross-determinant `W = ±1`) under the *algebraic* φ, via the Fibonacci convergents
(`FibCassiniNat`).  But the φ-Cassini identity is just the all-`1`s case of a universal
fact: **for *any* partial-quotient sequence, the continued-fraction convergents'
cross-determinant is a unit** (`W² = 1`).  Every irrational, presented by its continued
fraction, sits on the det-one floor — the floor is not special to φ, it is the universal
best-approximation locus.

  * `cfP`, `cfQ` — the convergent numerators/denominators of an arbitrary partial-quotient
    sequence `a : ℕ → ℕ` (`p_{n+2} = a_{n+2}·p_{n+1} + p_n`, `q` likewise), over `ℤ`.
  * ★★ `cf_det_step` — the **universal Cassini engine**: `W_{n+1} = −W_n`, where
    `W_n = p_{n+1}·q_n − p_n·q_{n+1}` (the `a`-terms cancel by commutativity).  The `q = 1`
    case of the general second-order recurrence engine.
  * ★★★ `cf_det_sq` — hence `W_n² = 1` for **every** `n` and **every** partial-quotient
    sequence: the continued-fraction cross-determinant is always a unit.  The det-one
    floor, universal over the reals — `FibCassiniNat` is the all-`1`s instance.
  * `cfQn` / `cfQn_fib` / `cfQn_pos` — the denominators as `ℕ` (the `ℤ` ones are their
    cast, `cfQ_eq_cast`), positive and Fibonacci-growing (`q_{n+2} ≥ q_{n+1} + q_n`) — the
    gaps `1/(q_n q_{n+1})` shrink at least geometrically.

The continued fraction is the **expansion engine** in its purest form: a distinction
(the floor) leaves a unit residue, and *that residue is the next operand*
(`x ↦ 1/(x − ⌊x⌋)`), re-entering the same distinction one scale down — a self-similar
chain, not an infinite regress (the tail of a continued fraction is again a continued
fraction).  It is **gapless** for two reasons made precise here: the step is the
*indivisible* unit `W = ±1` (`cf_det_sq` — nothing wedges between one convergent and the
next), and the denominators grow so the residue shrinks (`cfQn_fib`) — surplus fed back,
not space filled, with no exterior slot to leave empty.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuedFractionFloor

open E213.Meta.Algebra213 (Ring213 CommRing213)
open E213.Meta.Algebra213.Ring213
  (add_mul mul_add mul_assoc add_comm add_assoc neg_add neg_neg neg_mul mul_neg
   add_4_swap_mid neg_add_cancel_self add_zero zero_add)
open E213.Meta.Int213 (mul_one add_neg_cancel)
open E213.Meta.Algebra213.CommRing213 (mul_comm)

/-! ## §1 — the universal `q = 1` Cassini step over a commutative ring -/

/-- `A + B + −(A + C) = B + −C` over any `Ring213`. -/
theorem cancel_lemma {α} [Ring213 α] (A B C : α) : A + B + -(A + C) = B + -C := by
  rw [neg_add, add_4_swap_mid A B (-A) (-C), add_comm A (-A), neg_add_cancel_self, zero_add]

/-- ★ **The `q = 1` Cassini step.**  `(p·x + y)·z − x·(p·z + w) = y·z − x·w` over any
    commutative ring — the `p`-terms cancel.  The engine behind the continued-fraction
    determinant. -/
theorem cassini_one {α} [CommRing213 α] (p x y z w : α) :
    (p*x + y)*z + -(x*(p*z + w)) = y*z + -(x*w) := by
  have hE : p*x*z = x*(p*z) := by rw [mul_comm p x, mul_assoc]
  calc (p*x + y)*z + -(x*(p*z + w))
      = x*(p*z) + y*z + -(x*(p*z) + x*w) := by rw [add_mul, mul_add, hE]
    _ = y*z + -(x*w) := cancel_lemma _ _ _

/-! ## §2 — the continued-fraction convergents -/

/-- Convergent numerators of the partial-quotient sequence `a` (over `ℤ`):
    `p₀ = a₀`, `p₁ = a₁·a₀ + 1`, `p_{n+2} = a_{n+2}·p_{n+1} + p_n`. -/
def cfP (a : Nat → Nat) : Nat → Int
  | 0   => (a 0 : Int)
  | 1   => (a 1 : Int) * (a 0 : Int) + 1
  | n+2 => (a (n+2) : Int) * cfP a (n+1) + cfP a n

/-- Convergent denominators: `q₀ = 1`, `q₁ = a₁`, `q_{n+2} = a_{n+2}·q_{n+1} + q_n`. -/
def cfQ (a : Nat → Nat) : Nat → Int
  | 0   => 1
  | 1   => (a 1 : Int)
  | n+2 => (a (n+2) : Int) * cfQ a (n+1) + cfQ a n

/-- The convergent cross-determinant `W_n = p_{n+1}·q_n − p_n·q_{n+1}`. -/
def cfDet (a : Nat → Nat) (n : Nat) : Int :=
  cfP a (n+1) * cfQ a n + -(cfP a n * cfQ a (n+1))

/-! ## §3 — the universal Cassini and the det-one floor -/

/-- ★★ **The universal Cassini engine.**  `W_{n+1} = −W_n` for any partial quotients —
    the `a`-terms cancel (`cassini_one`). -/
theorem cf_det_step (a : Nat → Nat) (n : Nat) : cfDet a (n+1) = -(cfDet a n) := by
  show ((a (n+2) : Int) * cfP a (n+1) + cfP a n) * cfQ a (n+1)
        + -(cfP a (n+1) * ((a (n+2) : Int) * cfQ a (n+1) + cfQ a n))
     = -(cfP a (n+1) * cfQ a n + -(cfP a n * cfQ a (n+1)))
  rw [cassini_one (a (n+2) : Int) (cfP a (n+1)) (cfP a n) (cfQ a (n+1)) (cfQ a n),
      neg_add, neg_neg, add_comm]

/-- `W₀ = 1`: the base of the det-one floor (`p₁·q₀ − p₀·q₁ = (a₁a₀+1)·1 − a₀·a₁ = 1`). -/
theorem cf_det_zero (a : Nat → Nat) : cfDet a 0 = 1 := by
  show ((a 1 : Int) * (a 0 : Int) + 1) * 1 + -((a 0 : Int) * (a 1 : Int)) = 1
  rw [mul_one, mul_comm (a 1 : Int) (a 0 : Int), add_assoc, add_comm 1 (-((a 0 : Int)*(a 1 : Int))),
      ← add_assoc, add_neg_cancel, zero_add]

/-- ★★★ **The continued-fraction cross-determinant is universally a unit.**
    `W_n² = 1` for *every* `n` and *every* partial-quotient sequence — the det-one floor,
    universal over the reals.  The Fibonacci/φ case (`FibCassiniNat`) is the all-`1`s
    instance; here it holds for the continued fraction of any real. -/
theorem cf_det_sq (a : Nat → Nat) : ∀ n, cfDet a n * cfDet a n = 1 := by
  intro n
  induction n with
  | zero => rw [cf_det_zero, mul_one]
  | succ k ih =>
    rw [cf_det_step]
    show -(cfDet a k) * -(cfDet a k) = 1
    rw [neg_mul, mul_neg, neg_neg]
    exact ih

/-! ## §4 — the denominators grow (the residue shrinks) -/

/-- The convergent denominators as a `ℕ` sequence (the `ℤ` `cfQ` is their cast). -/
def cfQn (a : Nat → Nat) : Nat → Nat
  | 0   => 1
  | 1   => a 1
  | n+2 => a (n+2) * cfQn a (n+1) + cfQn a n

/-- `cfQ` is the `ℤ`-cast of `cfQn`. -/
theorem cfQ_eq_cast (a : Nat → Nat) : ∀ n, cfQ a n = (cfQn a n : Int)
  | 0   => rfl
  | 1   => rfl
  | n+2 => by
    show (a (n+2) : Int) * cfQ a (n+1) + cfQ a n = ((a (n+2) * cfQn a (n+1) + cfQn a n : Nat) : Int)
    rw [Int.ofNat_add, Int.ofNat_mul, cfQ_eq_cast a (n+1), cfQ_eq_cast a n]

/-- The denominators are positive (partial quotients `≥ 1`). -/
theorem cfQn_pos (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) : ∀ n, 1 ≤ cfQn a n
  | 0   => Nat.le_refl 1
  | 1   => ha 0
  | n+2 => Nat.le_trans (cfQn_pos a ha n) (Nat.le_add_left _ _)

/-- ★★ **The denominators grow at least like Fibonacci.**  `q_{n+2} ≥ q_{n+1} + q_n` (for
    partial quotients `≥ 1`), so `q_n ≥ Fib(n)` grows geometrically and the convergent
    gaps `|W_n|/(q_n q_{n+1}) = 1/(q_n q_{n+1})` shrink — the residue of the expansion
    chain shrinks at every step. -/
theorem cfQn_fib (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) (n : Nat) :
    cfQn a (n+1) + cfQn a n ≤ cfQn a (n+2) := by
  show cfQn a (n+1) + cfQn a n ≤ a (n+2) * cfQn a (n+1) + cfQn a n
  exact Nat.add_le_add_right (Nat.le_mul_of_pos_left (cfQn a (n+1)) (ha (n+1))) _

/-! ## §5 — the even two-step cross-determinant is a partial quotient -/

private theorem cancel_lemma2 {α} [Ring213 α] (A B C : α) : A + B + (C + -B) = A + C := by
  rw [add_4_swap_mid A B C (-B), add_comm B (-B), neg_add_cancel_self, add_zero]

/-- `a·(b·c) = b·(a·c)` over a commutative ring (derived from `mul_comm`/`mul_assoc`). -/
private theorem mul_lc {α} [CommRing213 α] (a b c : α) : a*(b*c) = b*(a*c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

/-- The two-step determinant in terms of the one-step: `(a·x₁+x₀)·z₀ − x₀·(a·z₁+z₀) =
    a·(x₁·z₀ − x₀·z₁)` over any commutative ring. -/
theorem det2_ring {α} [CommRing213 α] (a x1 x0 z1 z0 : α) :
    (a*x1 + x0)*z0 + -(x0*(a*z1 + z0)) = a*(x1*z0 + -(x0*z1)) := by
  calc (a*x1 + x0)*z0 + -(x0*(a*z1 + z0))
      = (a*x1)*z0 + x0*z0 + (-(x0*(a*z1)) + -(x0*z0)) := by rw [add_mul, mul_add, neg_add]
    _ = (a*x1)*z0 + -(x0*(a*z1)) := cancel_lemma2 _ _ _
    _ = a*(x1*z0) + -(a*(x0*z1)) := by rw [mul_assoc, mul_lc x0 a z1]
    _ = a*(x1*z0 + -(x0*z1)) := by rw [← mul_neg, ← mul_add]

/-- The two-step cross-determinant `W'_n = p_{n+2}·q_n − p_n·q_{n+2}`. -/
def cfDet2 (a : Nat → Nat) (n : Nat) : Int :=
  cfP a (n+2) * cfQ a n + -(cfP a n * cfQ a (n+2))

/-- ★★ **The two-step determinant is the partial quotient times the one-step.**
    `W'_n = a_{n+2}·W_n` (`det2_ring` on the convergent recurrence). -/
theorem cfDet2_eq (a : Nat → Nat) (n : Nat) :
    cfDet2 a n = (a (n+2) : Int) * cfDet a n := by
  show ((a (n+2) : Int) * cfP a (n+1) + cfP a n) * cfQ a n
        + -(cfP a n * ((a (n+2) : Int) * cfQ a (n+1) + cfQ a n))
     = (a (n+2) : Int) * (cfP a (n+1) * cfQ a n + -(cfP a n * cfQ a (n+1)))
  exact det2_ring (a (n+2) : Int) (cfP a (n+1)) (cfP a n) (cfQ a (n+1)) (cfQ a n)

/-- The cross-determinant at an even index is `+1` (`W_{2n} = (−1)^{2n} = 1`). -/
theorem cf_det_even (a : Nat → Nat) : ∀ n, cfDet a (2*n) = 1
  | 0     => cf_det_zero a
  | n+1 => by
    rw [Nat.mul_succ, cf_det_step, cf_det_step, neg_neg]
    exact cf_det_even a n

/-- ★★★ **The even two-step cross-determinant is the partial quotient.**
    `W'_{2n} = a_{2n+2}` — the cross-determinant of the (monotone-increasing) even
    convergents `p_{2n}/q_{2n}` is exactly the partial quotient `a_{2n+2}`.  This is the
    structural heart of universal completion: on the even convergents the floor's unit
    is amplified to the partial quotient, and the denominators grow with it. -/
theorem cfDet2_even (a : Nat → Nat) (n : Nat) :
    cfDet2 a (2*n) = (a (2*n + 2) : Int) := by
  rw [cfDet2_eq, cf_det_even, mul_one]

end E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuedFractionFloor
