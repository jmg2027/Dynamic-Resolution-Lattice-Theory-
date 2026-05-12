import E213.Lib.Math.Extras.CauchySchwarz
import E213.Meta.Tactic.Nat213

/-!
# n = 2 Cauchy-Schwarz (Σ-side aggregator, Nat-side, ∅-axiom)

Closes the "generic Σ-side Cauchy-Schwarz for n ≥ 2" residual
noted in `Extras/INDEX.md` and `Extras/CauchySchwarz.lean`.  This
file delivers the n=2 case.

Statement:
  `(a₁·b₁ + a₂·b₂)² ≤ (a₁² + a₂²) · (b₁² + b₂²)`

Proof: expand RHS and LHS, observe RHS − LHS contains the
cross-term `(a₁·b₂)² + (a₂·b₁)² − 2·(a₁·b₂)·(a₂·b₁) ≥ 0`, which
is the AM-GM atom `Extras.CauchySchwarz.two_mul_le_sq_add_sq`.
-/

namespace E213.Lib.Math.Extras.CauchySchwarz2D

open E213.Lib.Math.Extras.CauchySchwarz (two_mul_le_sq_add_sq)
open E213.Tactic.Nat213 (mul_assoc add_mul mul_mul_mul_comm_213)

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

end E213.Lib.Math.Extras.CauchySchwarz2D
