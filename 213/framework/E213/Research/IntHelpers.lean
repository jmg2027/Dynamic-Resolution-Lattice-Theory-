/-!
# Research: shared `Int` helpers

Two basic facts about integer self-multiplication used by every
quadratic-extension `Domain` module (ZIDomain, ZSqrt2Domain,
…).  Extracted here to remove duplication.

Both lemmas are pure Lean 4 core (no `ring`, no `nlinarith`).
-/

namespace E213.Research.IntHelpers

/-- `0 ≤ a*a` for any integer `a`. -/
protected theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have eq : (-a) * (-a) = a * a := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← eq]; exact Int.mul_nonneg h' h'

/-- `a*a = 0 ↔ a = 0` for any integer `a`. -/
protected theorem mul_self_eq_zero {a : Int} : a * a = 0 ↔ a = 0 := by
  refine ⟨?_, fun h => by rw [h]; simp⟩
  intro h
  rcases Int.mul_eq_zero.mp h with h' | h' <;> exact h'

end E213.Research.IntHelpers
