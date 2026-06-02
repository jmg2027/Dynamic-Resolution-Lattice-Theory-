import E213.Lib.Math.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaUnits
import E213.Meta.Algebra213.Core
import E213.Meta.Int213.Core

/-!
# EisensteinCrossDet — the cross-determinant of ℤ[ω]-convergents, and its unit floor

The real-quadratic side of the completability arc reads convergents `(a_i, d_i) ∈ ℤ²`
through their **cross-determinant** `W_i = a_{i+1}d_i − a_i d_{i+1} ∈ ℤ`, whose det-one
floor `W = ±1` (Cassini) is the φ/Fibonacci locus.  This file develops the **Eisenstein
analog over `ℤ[ω]`**: convergents `(a_i, d_i) ∈ ℤ[ω]²` with cross-determinant `W_i ∈
ℤ[ω]`, and the unit floor (the **6 units** of `ℤ[ω]`, vs the 2 units `±1` of `ℤ`).

  * ★ `cassini_ring` — the ring identity `(p·x+q·y)·z − x·(p·z+q·w) = q·(y·z − x·w)`,
    proved ∅-axiom over the commutative ring `ℤ[ω]` (manual `calc`, no normalizer).
  * ★★ `crossDet_step` — the **Cassini engine**: for two sequences obeying a common
    second-order recurrence `s_{n+2} = p·s_{n+1} + q·s_n`, the cross-determinant satisfies
    `W_{n+1} = −q·W_n` (the `p`-terms cancel by commutativity).
  * ★★ `crossDet_normSq_step` — taking norms (`normSq_mul`, `normSq_neg`):
    `‖W_{n+1}‖² = ‖q‖²·‖W_n‖²`.
  * ★★★ `crossDet_unit_floor` — if `q` and `W_0` are **units** (`‖·‖² = 1`), then
    `‖W_n‖² = 1` for **all** `n`: the cross-determinant stays on the unit floor.
  * ★★★ `crossDet_on_units` — hence each `W_n` is **literally one of the 6 units**
    (`ZOmegaUnits.normSq_one_in_units6`).  The Eisenstein analog of φ's Cassini floor:
    the ℤ[ω]-convergent cross-determinant rides the order-6 unit group.
  * `omegaFib` / `omega_fib_unit_floor` — a concrete ω-involving witness
    (`s_{n+2} = ω·s_n`, `q = ω`, `‖ω‖² = 1`) whose cross-determinant stays a unit.

All zero-axiom.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.EisensteinCrossDet

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Meta.Algebra213 (Ring213)
open E213.Meta.Algebra213.Ring213
  (add_mul mul_add mul_assoc add_comm neg_add mul_neg neg_neg add_4_swap_mid
   neg_add_cancel_self zero_add)
open E213.Meta.Algebra213.CommRing213 (mul_comm)

/-! ## §1 — the Cassini ring identity over ℤ[ω] -/

/-- `A + B + −(A + C) = B + −C` over any `Ring213` (the cancellation of `A`). -/
theorem cancel_lemma {α} [Ring213 α] (A B C : α) : A + B + -(A + C) = B + -C := by
  rw [neg_add, add_4_swap_mid A B (-A) (-C), add_comm A (-A), neg_add_cancel_self, zero_add]

/-- ★ **The Cassini ring identity** over `ℤ[ω]`:
    `(p·x + q·y)·z − x·(p·z + q·w) = q·(y·z − x·w)`.  The `p`-terms cancel by
    commutativity; `q` factors out.  Proved by manual `calc` with the pure `Ring213`
    API (no ring normalizer exists). -/
theorem cassini_ring (p q x y z w : ZOmega) :
    (p*x + q*y)*z - x*(p*z + q*w) = q*(y*z - x*w) := by
  show (p*x + q*y)*z + -(x*(p*z + q*w)) = q*(y*z + -(x*w))
  have hE1 : p*x*z = x*(p*z) := by rw [mul_comm p x, mul_assoc]
  have hE2 : q*y*z = q*(y*z) := by rw [mul_assoc]
  have hE3 : x*(q*w) = q*(x*w) := by rw [← mul_assoc, mul_comm x q, mul_assoc]
  calc (p*x + q*y)*z + -(x*(p*z + q*w))
      = x*(p*z) + q*(y*z) + -(x*(p*z) + q*(x*w)) := by rw [add_mul, mul_add, hE1, hE2, hE3]
    _ = q*(y*z) + -(q*(x*w)) := cancel_lemma _ _ _
    _ = q*(y*z) + q*(-(x*w)) := by rw [← mul_neg]
    _ = q*(y*z + -(x*w)) := by rw [← mul_add]

/-- `q·(Y − X) = −(q·(X − Y))`. -/
theorem qmul_antisym (q X Y : ZOmega) : q * (Y - X) = -(q * (X - Y)) := by
  show q * (Y + -X) = -(q * (X + -Y))
  have h : Y + -X = -(X + -Y) := by rw [neg_add, neg_neg, add_comm Y (-X)]
  rw [h, mul_neg]

/-! ## §2 — the cross-determinant and the Cassini engine -/

/-- The cross-determinant of `ℤ[ω]`-convergents: `W_n = a_{n+1}·d_n − a_n·d_{n+1}`. -/
def crossDet (a d : Nat → ZOmega) (n : Nat) : ZOmega :=
  a (n+1) * d n - a n * d (n+1)

/-- ★★ **The Cassini engine.**  For two sequences obeying a common second-order
    recurrence `s_{n+2} = p·s_{n+1} + q·s_n`, the cross-determinant satisfies
    `W_{n+1} = −q·W_n`. -/
theorem crossDet_step (a d : Nat → ZOmega) (p q : ZOmega)
    (ha : ∀ n, a (n+2) = p * a (n+1) + q * a n)
    (hd : ∀ n, d (n+2) = p * d (n+1) + q * d n) (n : Nat) :
    crossDet a d (n+1) = -(q * crossDet a d n) := by
  show a (n+2) * d (n+1) - a (n+1) * d (n+2)
     = -(q * (a (n+1) * d n - a n * d (n+1)))
  rw [ha n, hd n, cassini_ring p q (a (n+1)) (a n) (d (n+1)) (d n)]
  exact qmul_antisym q (a (n+1) * d n) (a n * d (n+1))

/-! ## §3 — the norm recurrence and the unit floor -/

/-- The Eisenstein norm is even: `‖−u‖² = ‖u‖²`. -/
theorem normSq_neg (u : ZOmega) : (-u).normSq = u.normSq := by
  show (-u.re) * (-u.re) - (-u.re) * (-u.im) + (-u.im) * (-u.im)
     = u.re * u.re - u.re * u.im + u.im * u.im
  rw [E213.Meta.Int213.neg_mul, E213.Meta.Int213.mul_neg, Int.neg_neg,
      E213.Meta.Int213.neg_mul, E213.Meta.Int213.mul_neg, Int.neg_neg,
      E213.Meta.Int213.neg_mul, E213.Meta.Int213.mul_neg, Int.neg_neg]

/-- ★★ **The norm recurrence**: `‖W_{n+1}‖² = ‖q‖²·‖W_n‖²`. -/
theorem crossDet_normSq_step (a d : Nat → ZOmega) (p q : ZOmega)
    (ha : ∀ n, a (n+2) = p * a (n+1) + q * a n)
    (hd : ∀ n, d (n+2) = p * d (n+1) + q * d n) (n : Nat) :
    (crossDet a d (n+1)).normSq = q.normSq * (crossDet a d n).normSq := by
  rw [crossDet_step a d p q ha hd n, normSq_neg, ZOmega.normSq_mul]

/-- ★★★ **The unit floor is preserved.**  If `q` and `W_0` are units (`‖·‖² = 1`), then
    `‖W_n‖² = 1` for every `n` — the cross-determinant stays on the unit floor. -/
theorem crossDet_unit_floor (a d : Nat → ZOmega) (p q : ZOmega)
    (ha : ∀ n, a (n+2) = p * a (n+1) + q * a n)
    (hd : ∀ n, d (n+2) = p * d (n+1) + q * d n)
    (hq : q.normSq = 1) (h0 : (crossDet a d 0).normSq = 1) :
    ∀ n, (crossDet a d n).normSq = 1 := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih =>
    rw [crossDet_normSq_step a d p q ha hd k, hq, ih]
    decide

/-- ★★★ **The cross-determinant rides the 6-unit group.**  Under the unit-floor
    hypotheses, every `W_n` is literally one of the 6 units of `ℤ[ω]`
    (`ZOmegaUnits.normSq_one_in_units6`).  The Eisenstein analog of φ's Cassini
    det-one floor (`W = ±1`, the 2 units of `ℤ`): over the hexagonal `ℤ[ω]` the
    cross-determinant floor is the order-6 unit group. -/
theorem crossDet_on_units (a d : Nat → ZOmega) (p q : ZOmega)
    (ha : ∀ n, a (n+2) = p * a (n+1) + q * a n)
    (hd : ∀ n, d (n+2) = p * d (n+1) + q * d n)
    (hq : q.normSq = 1) (h0 : (crossDet a d 0).normSq = 1) (n : Nat) :
    units6.contains (crossDet a d n) = true :=
  normSq_one_in_units6 (crossDet a d n)
    (crossDet_unit_floor a d p q ha hd hq h0 n)

/-! ## §4 — a concrete ω-Fibonacci witness -/

/-- A second-order `ℤ[ω]`-recurrence `s_{n+2} = p·s_{n+1} + q·s_n` from seeds. -/
def efib (p q s0 s1 : ZOmega) : Nat → ZOmega
  | 0   => s0
  | 1   => s1
  | n+2 => p * efib p q s0 s1 (n+1) + q * efib p q s0 s1 n

theorem efib_rec (p q s0 s1 : ZOmega) (n : Nat) :
    efib p q s0 s1 (n+2) = p * efib p q s0 s1 (n+1) + q * efib p q s0 s1 n := rfl

/-- The ω-Fibonacci numerator/denominator: `s_{n+2} = 1·s_{n+1} + ω·s_n` (`q = ω`,
    `‖ω‖² = 1`). -/
def aFib : Nat → ZOmega := efib (ZOmega.ofInt 1) ZOmega.Omega 0 (ZOmega.ofInt 1)
def dFib : Nat → ZOmega := efib (ZOmega.ofInt 1) ZOmega.Omega (ZOmega.ofInt 1) 0

/-- ★★★ **The ω-Fibonacci cross-determinant rides the 6-unit floor.**  A genuinely
    ω-involving recurrence (`q = ω`) whose cross-determinant is one of the 6 units of
    `ℤ[ω]` at every step — the concrete Eisenstein analog of φ's Fibonacci–Cassini
    `W = ±1`. -/
theorem omegaFib_on_units (n : Nat) :
    units6.contains (crossDet aFib dFib n) = true :=
  crossDet_on_units aFib dFib (ZOmega.ofInt 1) ZOmega.Omega
    (fun n => efib_rec (ZOmega.ofInt 1) ZOmega.Omega 0 (ZOmega.ofInt 1) n)
    (fun n => efib_rec (ZOmega.ofInt 1) ZOmega.Omega (ZOmega.ofInt 1) 0 n)
    (by decide) (by decide) n

end E213.Lib.Math.CayleyDickson.Integer.EisensteinCrossDet
