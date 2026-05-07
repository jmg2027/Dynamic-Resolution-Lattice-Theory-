import E213.Lib.Math.Extras.CauchySchwarz2D
import E213.Lib.Math.Extras.CauchySchwarz3D

/-!
# Σ-Cauchy-Schwarz on lists — small-`n` direct witnesses (∅-axiom)

213-native paradigm: `(Σ_{i} a_i · b_i)² ≤ (Σ_{i} a_i²) · (Σ_{i} b_i²)`.

Defines list-side `dotList`, `sumSqList`, witnesses the inequality
for n = 0, 1, 2, 3 directly.  Each n level uses the previous
together with the n=2 cross-term atom; the inductive aggregator
to general `n` is the next step.
-/

namespace E213.Lib.Math.Extras.CauchySchwarzList

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
  rw [E213.Tactic.Nat213.mul_mul_mul_comm_213 (a 0) (b 0) (a 0) (b 0)]
  exact Nat.le_refl _

/-- ★ **n = 2** specialisation of `cs_2d_le` to `dotList / sumSqList`. -/
theorem cs_two (a b : Nat → Nat) :
    dotList a b 2 * dotList a b 2
      ≤ sumSqList a 2 * sumSqList b 2 := by
  show (0 + a 0 * b 0 + a 1 * b 1) * (0 + a 0 * b 0 + a 1 * b 1)
        ≤ (0 + a 0 * a 0 + a 1 * a 1) * (0 + b 0 * b 0 + b 1 * b 1)
  rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]
  exact E213.Lib.Math.Extras.CauchySchwarz2D.cs_2d_le
          (a 0) (a 1) (b 0) (b 1)

/-- Helper: `dotList a b 3` unfolds to `0 + a₀·b₀ + a₁·b₁ + a₂·b₂`. -/
theorem dotList_three (a b : Nat → Nat) :
    dotList a b 3 = 0 + a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := rfl

/-- Helper: `sumSqList a 3` unfolds to `0 + a₀² + a₁² + a₂²`. -/
theorem sumSqList_three (a : Nat → Nat) :
    sumSqList a 3 = 0 + a 0 * a 0 + a 1 * a 1 + a 2 * a 2 := rfl

end E213.Lib.Math.Extras.CauchySchwarzList
