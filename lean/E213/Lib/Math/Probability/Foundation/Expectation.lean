import E213.Lib.Math.Probability.Foundation.Bernoulli

/-!
# Probability — `Expectation`

Expected value as **atomic weighted counting**.

For a Bernoulli with success probability `p`, indicator `X ∈ {0, 1}`:
  `E[X] = 1 · p + 0 · (1 − p) = p`.

For a discrete distribution `[(mass_i, value_i)]` with common denominator
`D`, the expected value's numerator is `Σ mass_i · value_i` over `D`.

213-native: no integral, no σ-algebra.  Just weighted sums of `Nat`s.
-/

namespace E213.Lib.Math.Probability.Foundation.Expectation

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Foundation.Bernoulli (Bernoulli)

/-- Bernoulli expectation: `E[X] = p` (success probability). -/
def bernoulli (b : Bernoulli) : ProbabilityCut := b.success

/-- Discrete expectation numerator: `Σ mass_i · value_i` for a list of
    (mass-numerator, value) pairs with common denominator `D`. -/
def discreteNum : List (Nat × Nat) → Nat
  | [] => 0
  | (m, v) :: rest => m * v + discreteNum rest

/-- Discrete expectation `E[X] = (Σ mass_i · value_i) / D`. -/
def discrete (D : Nat) (xs : List (Nat × Nat)) : Nat × Nat :=
  (discreteNum xs, D)

/-- ★ Expectation master — Bernoulli rfl identities (fair, certain,
    impossible) + discrete-sum rfl/singleton + K_{3,2} pair / AB-indicator
    witnesses.  STRICT ∅-AXIOM. -/
theorem expectation_master :
    -- Fair coin E[X] = 1/2
    (bernoulli Bernoulli.fair).num = 1 ∧ (bernoulli Bernoulli.fair).den = 2
    -- Certain / impossible Bernoulli
    ∧ (bernoulli Bernoulli.certain).num = 1
    ∧ (bernoulli Bernoulli.impossible).num = 0
    -- Discrete identities
    ∧ discreteNum [] = 0
    ∧ (∀ m v : Nat, discreteNum [(m, v)] = m * v)
    -- K_{3,2} pair expectation: AA→0, BB→1, AB→2 ⇒ 13/10
    ∧ discreteNum [(3, 0), (1, 1), (6, 2)] = 13
    -- AB-or-not expectation = 6/10
    ∧ discreteNum [(3, 0), (1, 0), (6, 1)] = 6 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro m v
    show m * v + 0 = m * v
    exact Nat.add_zero (m * v)
  · decide
  · decide


/-- ★ **Discrete expectation numerator is additive over concatenation**:
    `Σ(mass·value)` of `xs ++ ys` splits as the sum over `xs` plus the sum over `ys`
    (linearity of expectation, numerator form). -/
theorem discreteNum_append : ∀ (xs ys : List (Nat × Nat)),
    discreteNum (xs ++ ys) = discreteNum xs + discreteNum ys
  | [],            ys => by show discreteNum ys = 0 + discreteNum ys; rw [Nat.zero_add]
  | (m, v) :: xs,  ys => by
      show m * v + discreteNum (xs ++ ys) = (m * v + discreteNum xs) + discreteNum ys
      rw [discreteNum_append xs ys, Nat.add_assoc]
end E213.Lib.Math.Probability.Foundation.Expectation
