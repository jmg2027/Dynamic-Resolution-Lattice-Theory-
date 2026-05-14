import E213.Meta.Tactic.NatHelper
/-!
# Five.lean helpers — ∅-axiom (Nat-arith + Bézout shifts)

Splits out the arithmetic helper lemmas needed by
`Theory/Atomicity/Five.atomic_implies_five`.  Pure ℕ, no `omega`,
no `simp`.  All theorems verified ∅-axiom.

The two main moves are:
  1. **Bézout shifts** `2*a + 3*b = 2*(a-3) + 3*(b+2)` and the
     symmetric form, used to surface a *second* decomposition that
     contradicts atomicity.
  2. **add-3-ne-self / add-2-ne-self** — the contradictions that
     follow from the shifted decomposition matching the original
     under the uniqueness clause.
-/

open E213.Tactic.NatHelper

namespace E213.Theory.Atomicity.FiveHelpers

/-- `b + 2 ≠ b`. -/
theorem add_two_ne_self (b : Nat) : b + 2 ≠ b := fun h =>
  let h_eq : b + 2 = b + 0 := h.trans (Nat.add_zero b).symm
  absurd (add_left_cancel h_eq) (by decide)

/-- `a + 3 ≠ a`. -/
theorem add_three_ne_self (a : Nat) : a + 3 ≠ a := fun h =>
  let h_eq : a + 3 = a + 0 := h.trans (Nat.add_zero a).symm
  absurd (add_left_cancel h_eq) (by decide)

end E213.Theory.Atomicity.FiveHelpers

namespace E213.Theory.Atomicity.FiveHelpers

/-- Bézout shift left: `3 ≤ a → 2*a + 3*b = 2*(a-3) + 3*(b+2)`. -/
theorem bezout_left {a b : Nat} (ha : 3 ≤ a) :
    2 * a + 3 * b = 2 * (a - 3) + 3 * (b + 2) := by
  have h1 : 2 * (a - 3) = 2 * a - 6 := mul_sub_distrib ha
  have h2 : 3 * (b + 2) = 3 * b + 6 := Nat.mul_add 3 b 2
  have h6 : 6 ≤ 2 * a := Nat.mul_le_mul_left 2 ha
  have step1 : (2 * a - 6) + (3 * b + 6) = (2 * a - 6) + (6 + 3 * b) :=
    congrArg (2 * a - 6 + ·) (Nat.add_comm (3 * b) 6)
  have step2 : (2 * a - 6) + (6 + 3 * b) = ((2 * a - 6) + 6) + 3 * b :=
    (Nat.add_assoc _ _ _).symm
  have step3 : (2 * a - 6) + 6 = 2 * a := sub_add_cancel h6
  have step4 : ((2 * a - 6) + 6) + 3 * b = 2 * a + 3 * b :=
    congrArg (· + 3 * b) step3
  have h_a : 2 * (a - 3) + 3 * (b + 2) = (2 * a - 6) + 3 * (b + 2) :=
    congrArg (· + 3 * (b + 2)) h1
  have h_b : (2 * a - 6) + 3 * (b + 2) = (2 * a - 6) + (3 * b + 6) :=
    congrArg ((2 * a - 6) + ·) h2
  have h_combined : 2 * (a - 3) + 3 * (b + 2) = 2 * a + 3 * b :=
    (h_a.trans h_b).trans (step1.trans (step2.trans step4))
  exact h_combined.symm

/-- Bézout shift right: `2 ≤ b → 2*a + 3*b = 2*(a+3) + 3*(b-2)`. -/
theorem bezout_right {a b : Nat} (hb : 2 ≤ b) :
    2 * a + 3 * b = 2 * (a + 3) + 3 * (b - 2) := by
  have h1 : 2 * (a + 3) = 2 * a + 6 := Nat.mul_add 2 a 3
  have h2 : 3 * (b - 2) = 3 * b - 6 := mul_sub_distrib hb
  have h6 : 6 ≤ 3 * b := Nat.mul_le_mul_left 3 hb
  have step1 : (2 * a + 6) + (3 * b - 6) = 2 * a + (6 + (3 * b - 6)) :=
    Nat.add_assoc _ _ _
  have step2 : 6 + (3 * b - 6) = (3 * b - 6) + 6 := Nat.add_comm _ _
  have step3 : (3 * b - 6) + 6 = 3 * b := sub_add_cancel h6
  have step4 : 2 * a + (6 + (3 * b - 6)) = 2 * a + 3 * b :=
    congrArg (2 * a + ·) (step2.trans step3)
  have h_a : 2 * (a + 3) + 3 * (b - 2) = (2 * a + 6) + 3 * (b - 2) :=
    congrArg (· + 3 * (b - 2)) h1
  have h_b : (2 * a + 6) + 3 * (b - 2) = (2 * a + 6) + (3 * b - 6) :=
    congrArg ((2 * a + 6) + ·) h2
  have h_combined : 2 * (a + 3) + 3 * (b - 2) = 2 * a + 3 * b :=
    (h_a.trans h_b).trans (step1.trans step4)
  exact h_combined.symm

end E213.Theory.Atomicity.FiveHelpers
