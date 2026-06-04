import E213.Meta.Tactic.NatHelper

/-!
# Extras.CauchySchwarz — Cauchy-Schwarz family (atomic, ∅-axiom)

Atomic Nat-side Cauchy-Schwarz inequality + per-dimension and
list variants:

| Section | Topic |
|---|---|
| `CauchySchwarz` | Base: `2 · a · b ≤ a² + b²` for `a, b : Nat` |
| `CauchySchwarz2D` | n = 2 Σ-aggregator |
| `CauchySchwarz3D` | n = 3 extension |
| `CauchySchwarz4D` | n = 4 extension |
| `CauchySchwarzList` | List-side aggregator |
| `CauchySchwarzInductive` | inductive form |

Per-variant namespaces preserved (external HurwitzExactL1 cites
`Extras.CauchySchwarz`).
-/

namespace E213.Lib.Math.Tactic.Extras.CauchySchwarz

open E213.Tactic.NatHelper (mul_assoc add_mul)

/-- Term-mode `(a + d)² = a² + 2·a·d + d²`. -/
theorem sq_add (a d : Nat) :
    (a + d) * (a + d) = a * a + 2 * (a * d) + d * d := by
  show (a + d) * (a + d) = a * a + 2 * (a * d) + d * d
  rw [Nat.mul_add (a + d) a d]
  rw [add_mul a d a, add_mul a d d]
  rw [Nat.mul_comm d a]
  show a * a + a * d + (a * d + d * d) = a * a + 2 * (a * d) + d * d
  rw [← Nat.add_assoc (a * a + a * d) (a * d) (d * d)]
  rw [Nat.add_assoc (a * a) (a * d) (a * d)]
  show a * a + (a * d + a * d) + d * d = a * a + 2 * (a * d) + d * d
  show a * a + (a * d + a * d) + d * d = a * a + 2 * (a * d) + d * d
  have h : a * d + a * d = 2 * (a * d) := by
    show a * d + a * d = (1 + 1) * (a * d)
    rw [add_mul 1 1 (a * d), Nat.one_mul]
  rw [h]

/-- Term-mode helper: `a + a = 2 · a`. -/
theorem add_self_eq_two_mul (a : Nat) : a + a = 2 * a := by
  show a + a = (1 + 1) * a
  rw [add_mul 1 1 a, Nat.one_mul]

/-- Algebraic identity in `(a, d)` form:
    `a² + (a+d)² = 2·a·(a+d) + d²`. -/
theorem cs_expand (a d : Nat) :
    a * a + (a + d) * (a + d) = 2 * (a * (a + d)) + d * d := by
  rw [sq_add a d]
  show a * a + (a * a + 2 * (a * d) + d * d)
        = 2 * (a * (a + d)) + d * d
  rw [Nat.mul_add a a d, Nat.mul_add 2 (a * a) (a * d)]
  rw [Nat.add_assoc (a * a) (a * a + 2 * (a * d)) (d * d)
        |>.symm]
  show (a * a + (a * a + 2 * (a * d))) + d * d
        = 2 * (a * a) + 2 * (a * d) + d * d
  rw [Nat.add_assoc (a * a) (a * a) (2 * (a * d)) |>.symm]
  show (a * a + a * a + 2 * (a * d)) + d * d
        = 2 * (a * a) + 2 * (a * d) + d * d
  rw [add_self_eq_two_mul (a * a)]

/-- ★ AM-GM-style cross term: `2·a·b ≤ a² + b²` (Cauchy-Schwarz
    on a 1-bracket cover, Nat side; ∅-axiom). -/
theorem two_mul_le_sq_add_sq (a b : Nat) :
    2 * (a * b) ≤ a * a + b * b := by
  rcases Nat.le_total a b with hab | hba
  · -- case a ≤ b: write b as a + (b - a) = a + d
    have hb : a + (b - a) = b := E213.Tactic.NatHelper.add_sub_of_le hab
    have hgoal : 2 * (a * (a + (b - a))) ≤
                 a * a + (a + (b - a)) * (a + (b - a)) := by
      rw [cs_expand a (b - a)]
      exact Nat.le_add_right _ _
    rw [hb] at hgoal
    exact hgoal
  · -- case b ≤ a: symmetric.  Swap and reduce.
    have ha : b + (a - b) = a := E213.Tactic.NatHelper.add_sub_of_le hba
    have hgoal : 2 * (b * (b + (a - b))) ≤
                 b * b + (b + (a - b)) * (b + (a - b)) := by
      rw [cs_expand b (a - b)]
      exact Nat.le_add_right _ _
    rw [ha] at hgoal
    -- hgoal : 2 * (b * a) ≤ b * b + a * a
    rw [Nat.mul_comm a b, Nat.add_comm (a * a) (b * b)]
    exact hgoal

end E213.Lib.Math.Tactic.Extras.CauchySchwarz

namespace E213.Lib.Math.Tactic.Extras.CauchySchwarz2D

open E213.Lib.Math.Tactic.Extras.CauchySchwarz (two_mul_le_sq_add_sq)
open E213.Tactic.NatHelper (mul_assoc add_mul mul_mul_mul_comm_213)

/-- Helper — squared expansion of `(x + y)²`. -/
theorem sq_add_two (x y : Nat) :
    (x + y) * (x + y) = x * x + 2 * (x * y) + y * y := by
  rw [Nat.mul_add (x + y) x y, add_mul x y x, add_mul x y y]
  rw [Nat.mul_comm y x]
  rw [← Nat.add_assoc (x * x + x * y) (x * y) (y * y)]
  rw [Nat.add_assoc (x * x) (x * y) (x * y)]
  have h2 : x * y + x * y = 2 * (x * y) := by
    show x * y + x * y = (1 + 1) * (x * y)
    rw [add_mul 1 1 (x * y), Nat.one_mul]
  rw [h2]

/-- Term-mode `a + b + (c + d) = a + c + (b + d)`. -/
theorem add_swap_middle4 (a b c d : Nat) :
    a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d)]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [← Nat.add_assoc a c (b + d)]

/-- Helper — RHS expansion. -/
theorem rhs_expand (a1 a2 b1 b2 : Nat) :
    (a1 * a1 + a2 * a2) * (b1 * b1 + b2 * b2)
      = a1 * a1 * (b1 * b1) + a1 * a1 * (b2 * b2)
        + (a2 * a2 * (b1 * b1) + a2 * a2 * (b2 * b2)) := by
  rw [Nat.mul_add (a1 * a1 + a2 * a2) (b1 * b1) (b2 * b2)]
  rw [add_mul (a1 * a1) (a2 * a2) (b1 * b1)]
  rw [add_mul (a1 * a1) (a2 * a2) (b2 * b2)]
  exact add_swap_middle4 (a1*a1*(b1*b1)) (a2*a2*(b1*b1))
        (a1*a1*(b2*b2)) (a2*a2*(b2*b2))

/-- Cross-term inequality: `2 · (a₁·b₁) · (a₂·b₂) ≤ a₁²·b₂² + a₂²·b₁²`,
    via the AM-GM atom applied to `(a₁·b₂, a₂·b₁)`. -/
theorem cross_term_le (a1 a2 b1 b2 : Nat) :
    2 * ((a1 * b1) * (a2 * b2))
      ≤ a1 * a1 * (b2 * b2) + a2 * a2 * (b1 * b1) := by
  have h := two_mul_le_sq_add_sq (a1 * b2) (a2 * b1)
  -- h : 2 * ((a1·b2) · (a2·b1)) ≤ (a1·b2)² + (a2·b1)²
  have e1 : (a1 * b2) * (a2 * b1) = (a1 * b1) * (a2 * b2) := by
    rw [mul_mul_mul_comm_213 a1 b2 a2 b1]
    rw [Nat.mul_comm b2 b1]
    rw [mul_mul_mul_comm_213 a1 a2 b1 b2]
  rw [e1] at h
  rw [mul_mul_mul_comm_213 a1 b2 a1 b2] at h
  rw [mul_mul_mul_comm_213 a2 b1 a2 b1] at h
  exact h

/-- LHS expansion: `(a₁b₁ + a₂b₂)² = (a₁b₁)² + 2·(a₁b₁)·(a₂b₂) + (a₂b₂)²`. -/
theorem lhs_expand (a1 a2 b1 b2 : Nat) :
    (a1 * b1 + a2 * b2) * (a1 * b1 + a2 * b2)
      = (a1 * b1) * (a1 * b1) + 2 * ((a1 * b1) * (a2 * b2))
        + (a2 * b2) * (a2 * b2) :=
  sq_add_two (a1 * b1) (a2 * b2)

/-- ★ **n=2 Cauchy-Schwarz** (Σ-side, ∅-axiom):
    `(a₁·b₁ + a₂·b₂)² ≤ (a₁² + a₂²)·(b₁² + b₂²)`. -/
theorem cs_2d_le (a1 a2 b1 b2 : Nat) :
    (a1 * b1 + a2 * b2) * (a1 * b1 + a2 * b2)
      ≤ (a1 * a1 + a2 * a2) * (b1 * b1 + b2 * b2) := by
  rw [lhs_expand a1 a2 b1 b2, rhs_expand a1 a2 b1 b2]
  rw [mul_mul_mul_comm_213 a1 b1 a1 b1]
  rw [mul_mul_mul_comm_213 a2 b2 a2 b2]
  -- LHS: a1²b1² + 2(a1b1)(a2b2) + a2²b2²
  -- RHS: a1²b1² + a1²b2² + (a2²b1² + a2²b2²)
  -- Cross: 2(a1b1)(a2b2) ≤ a1²b2² + a2²b1²
  rw [Nat.add_assoc (a1 * a1 * (b1 * b1)) (a1 * a1 * (b2 * b2))
        (a2 * a2 * (b1 * b1) + a2 * a2 * (b2 * b2))]
  -- target: a1²b1² + 2·(...)  + a2²b2²
  --       ≤ a1²b1² + (a1²b2² + (a2²b1² + a2²b2²))
  -- Rearrange RHS: a1²b1² + (a1²b2² + a2²b1²) + a2²b2²
  rw [← Nat.add_assoc (a1 * a1 * (b2 * b2)) (a2 * a2 * (b1 * b1))
        (a2 * a2 * (b2 * b2))]
  rw [← Nat.add_assoc (a1 * a1 * (b1 * b1))
        (a1 * a1 * (b2 * b2) + a2 * a2 * (b1 * b1))
        (a2 * a2 * (b2 * b2))]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact cross_term_le a1 a2 b1 b2

end E213.Lib.Math.Tactic.Extras.CauchySchwarz2D

namespace E213.Lib.Math.Tactic.Extras.CauchySchwarz3D

open E213.Lib.Math.Tactic.Extras.CauchySchwarz2D
  (cross_term_le sq_add_two)
open E213.Tactic.NatHelper (mul_assoc add_mul mul_mul_mul_comm_213)

/-- ★ **3D Cauchy-Schwarz cross-term aggregator** —
    `2·(a₁b₁)·(a₂b₂) + 2·(a₁b₁)·(a₃b₃) + 2·(a₂b₂)·(a₃b₃)
     ≤ (a₁²·b₂² + a₂²·b₁²) + (a₁²·b₃² + a₃²·b₁²)
       + (a₂²·b₃² + a₃²·b₂²)`. -/
theorem cs_3d_cross_aggregate (a1 a2 a3 b1 b2 b3 : Nat) :
    2 * ((a1 * b1) * (a2 * b2)) + 2 * ((a1 * b1) * (a3 * b3))
      + 2 * ((a2 * b2) * (a3 * b3))
    ≤ (a1*a1*(b2*b2) + a2*a2*(b1*b1))
      + (a1*a1*(b3*b3) + a3*a3*(b1*b1))
      + (a2*a2*(b3*b3) + a3*a3*(b2*b2)) := by
  have h12 := cross_term_le a1 a2 b1 b2
  have h13 := cross_term_le a1 a3 b1 b3
  have h23 := cross_term_le a2 a3 b2 b3
  exact Nat.add_le_add (Nat.add_le_add h12 h13) h23

end E213.Lib.Math.Tactic.Extras.CauchySchwarz3D

namespace E213.Lib.Math.Tactic.Extras.CauchySchwarz4D

open E213.Lib.Math.Tactic.Extras.CauchySchwarz2D (cross_term_le)

/-- ★ **4D cross-term aggregate** — 6 pair applications of the
    n=2 cross-term inequality.  -/
theorem cs_4d_cross_aggregate (a1 a2 a3 a4 b1 b2 b3 b4 : Nat) :
    2 * ((a1 * b1) * (a2 * b2)) + 2 * ((a1 * b1) * (a3 * b3))
    + 2 * ((a1 * b1) * (a4 * b4)) + 2 * ((a2 * b2) * (a3 * b3))
    + 2 * ((a2 * b2) * (a4 * b4)) + 2 * ((a3 * b3) * (a4 * b4))
    ≤ (a1*a1*(b2*b2) + a2*a2*(b1*b1))
      + (a1*a1*(b3*b3) + a3*a3*(b1*b1))
      + (a1*a1*(b4*b4) + a4*a4*(b1*b1))
      + (a2*a2*(b3*b3) + a3*a3*(b2*b2))
      + (a2*a2*(b4*b4) + a4*a4*(b2*b2))
      + (a3*a3*(b4*b4) + a4*a4*(b3*b3)) := by
  have h12 := cross_term_le a1 a2 b1 b2
  have h13 := cross_term_le a1 a3 b1 b3
  have h14 := cross_term_le a1 a4 b1 b4
  have h23 := cross_term_le a2 a3 b2 b3
  have h24 := cross_term_le a2 a4 b2 b4
  have h34 := cross_term_le a3 a4 b3 b4
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add h12 h13) h14) h23) h24) h34

end E213.Lib.Math.Tactic.Extras.CauchySchwarz4D

namespace E213.Lib.Math.Tactic.Extras.CauchySchwarzList

/-- Pointwise dot product over the first `n` indices. -/
def dotList (a b : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => dotList a b n + a n * b n

/-- Pointwise sum of squares over the first `n` indices. -/
def sumSqList (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumSqList a n + a n * a n

/-- ★ **n = 0 base**: empty dot product squared = 0 ≤ 0. -/
theorem cs_zero (a b : Nat → Nat) :
    dotList a b 0 * dotList a b 0
      ≤ sumSqList a 0 * sumSqList b 0 :=
  Nat.le_refl 0

/-- ★ **n = 1**: `(a₀·b₀)² = a₀²·b₀²` (equality). -/
theorem cs_one (a b : Nat → Nat) :
    dotList a b 1 * dotList a b 1
      ≤ sumSqList a 1 * sumSqList b 1 := by
  show (0 + a 0 * b 0) * (0 + a 0 * b 0)
        ≤ (0 + a 0 * a 0) * (0 + b 0 * b 0)
  rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]
  rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213 (a 0) (b 0) (a 0) (b 0)]
  exact Nat.le_refl _

/-- ★ **n = 2** specialisation of `cs_2d_le` to `dotList / sumSqList`. -/
theorem cs_two (a b : Nat → Nat) :
    dotList a b 2 * dotList a b 2
      ≤ sumSqList a 2 * sumSqList b 2 := by
  show (0 + a 0 * b 0 + a 1 * b 1) * (0 + a 0 * b 0 + a 1 * b 1)
        ≤ (0 + a 0 * a 0 + a 1 * a 1) * (0 + b 0 * b 0 + b 1 * b 1)
  rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]
  exact E213.Lib.Math.Tactic.Extras.CauchySchwarz2D.cs_2d_le
          (a 0) (a 1) (b 0) (b 1)

/-- Helper: `dotList a b 3` unfolds to `0 + a₀·b₀ + a₁·b₁ + a₂·b₂`. -/
theorem dotList_three (a b : Nat → Nat) :
    dotList a b 3 = 0 + a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := rfl

/-- Helper: `sumSqList a 3` unfolds to `0 + a₀² + a₁² + a₂²`. -/
theorem sumSqList_three (a : Nat → Nat) :
    sumSqList a 3 = 0 + a 0 * a 0 + a 1 * a 1 + a 2 * a 2 := rfl

end E213.Lib.Math.Tactic.Extras.CauchySchwarzList

namespace E213.Lib.Math.Tactic.Extras.CauchySchwarzInductive

open E213.Lib.Math.Tactic.Extras.CauchySchwarz2D (cross_term_le)

/-- Cross-term sum at level `k`: `Σ_{i<k} 2 · (aᵢ·bᵢ) · (a_k·b_k)`. -/
def crossSum (a b : Nat → Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | i + 1 => crossSum a b i + 2 * ((a i * b i) * (a k * b k))

/-- Upper-bound sum at level `k`: `Σ_{i<k} (aᵢ² · b_k² + a_k² · bᵢ²)`. -/
def crossUpper (a b : Nat → Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | i + 1 => crossUpper a b i + (a i * a i * (b k * b k) + a k * a k * (b i * b i))

/-- ★ Cross sum at k=0 is 0 (rfl). -/
theorem crossSum_zero (a b : Nat → Nat) :
    crossSum a b 0 = 0 := rfl

/-- ★ Cross upper at k=0 is 0 (rfl). -/
theorem crossUpper_zero (a b : Nat → Nat) :
    crossUpper a b 0 = 0 := rfl

/-- ★ **Generic-n cross-term inequality** —
    `crossSum a b k ≤ crossUpper a b k` for every `k`,
    by induction.  Each step adds one n=2 cross-term application. -/
theorem crossSum_le_crossUpper : ∀ (a b : Nat → Nat) (k : Nat),
    crossSum a b k ≤ crossUpper a b k
  | _, _, 0 => Nat.le_refl 0
  | a, b, i + 1 => by
      show crossSum a b i + 2 * ((a i * b i) * (a (i+1) * b (i+1)))
        ≤ crossUpper a b i
          + (a i * a i * (b (i+1) * b (i+1))
             + a (i+1) * a (i+1) * (b i * b i))
      exact Nat.add_le_add (crossSum_le_crossUpper a b i)
                           (cross_term_le (a i) (a (i+1)) (b i) (b (i+1)))

end E213.Lib.Math.Tactic.Extras.CauchySchwarzInductive
