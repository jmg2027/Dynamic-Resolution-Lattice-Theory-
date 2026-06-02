import E213.Meta.Int213
import E213.Meta.Algebra213.Core

/-!
# ContinuedFractionFloor — every real's continued fraction sits on the det-one floor

`Cauchy/DepthFloorDetOne` and `Real213/CrossDetConstDenom` put the det-one floor
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

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.ContinuedFractionFloor

open E213.Meta.Algebra213 (Ring213 CommRing213)
open E213.Meta.Algebra213.Ring213
  (add_mul mul_add mul_assoc add_comm add_assoc neg_add neg_neg neg_mul mul_neg
   add_4_swap_mid neg_add_cancel_self zero_add)
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

end E213.Lib.Math.Real213.ContinuedFractionFloor
