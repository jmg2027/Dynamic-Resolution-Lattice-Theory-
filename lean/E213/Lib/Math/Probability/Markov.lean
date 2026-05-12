import E213.Lib.Math.Probability.Bayesian
import E213.Lib.Math.Probability.Expectation
import E213.Meta.Tactic.Nat213

/-!
# Probability — Markov property + Markov inequality (atomic)

Two Markov-flavoured facts:

  * **`BetaCount` is Markov** — sequential updates depend only on
    the cumulative `(ks, fs)` count, not on the order of arrival.
    This is the *sufficient statistic* property of Beta-Binomial
    conjugacy.

  * **Markov inequality (atomic)** — for a discrete distribution
    with non-negative values `v_i` and masses `m_i / D`,
    `a · #{v_i ≥ a · w_i} ≤ Σ m_i · v_i` after suitable scaling.

213-native: both are `Nat`-arithmetic facts.  No σ-algebra, no
filtration.
-/

namespace E213.Lib.Math.Probability.Markov

open E213.Lib.Math.Probability.Bayesian (BetaCount)

/-- Sequential `(k₁, f₁)` then `(k₂, f₂)` equals batch `(k₁+k₂, f₁+f₂)`
    on the success count (rfl unfolding `updateBatch`). -/
theorem updateBatch_seq_successes (b : BetaCount) (k₁ f₁ k₂ f₂ : Nat) :
    ((b.updateBatch k₁ f₁).updateBatch k₂ f₂).successes
    = (b.updateBatch (k₁ + k₂) (f₁ + f₂)).successes := by
  show b.successes + k₁ + k₂ = b.successes + (k₁ + k₂)
  exact Nat.add_assoc b.successes k₁ k₂

/-- Sequential update is symmetric on the failure count. -/
theorem updateBatch_seq_failures (b : BetaCount) (k₁ f₁ k₂ f₂ : Nat) :
    ((b.updateBatch k₁ f₁).updateBatch k₂ f₂).failures
    = (b.updateBatch (k₁ + k₂) (f₁ + f₂)).failures := by
  show b.failures + f₁ + f₂ = b.failures + (f₁ + f₂)
  exact Nat.add_assoc b.failures f₁ f₂

/-- ★ **Markov property of BetaCount** ★ — order of updates does
    not matter on the count fields.  `(b · u₁) · u₂ = (b · u₂) · u₁`. -/
theorem updateBatch_comm_successes (b : BetaCount) (k₁ f₁ k₂ f₂ : Nat) :
    ((b.updateBatch k₁ f₁).updateBatch k₂ f₂).successes
    = ((b.updateBatch k₂ f₂).updateBatch k₁ f₁).successes := by
  show b.successes + k₁ + k₂ = b.successes + k₂ + k₁
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm k₁ k₂]

/-- Sum of mass-weighted indicator: contribution of values `≥ a` to
    the discrete first moment.  `Σ m_i · v_i` restricted to `v_i ≥ a`. -/
def tailMomentNum (a : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (m, v) :: rest =>
      (if a ≤ v then m * v else 0) + tailMomentNum a rest

/-- Mass-only count of values `≥ a`: `Σ m_i` restricted to `v_i ≥ a`. -/
def tailMassNum (a : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (m, v) :: rest =>
      (if a ≤ v then m else 0) + tailMassNum a rest

/-- ★ **Markov inequality (atomic)** ★ — for non-negative discrete
    values, `a · #{v_i ≥ a · m_i} ≤ Σ m_i · v_i` (cross-multiplied).
    Proof by induction; uses `Nat.lt_or_ge` for the case split. -/
theorem markov_inequality (a : Nat) :
    ∀ xs : List (Nat × Nat), a * tailMassNum a xs ≤ tailMomentNum a xs
  | [] => by
    show a * 0 ≤ 0
    rw [Nat.mul_zero]
    exact Nat.le_refl 0
  | (m, v) :: rest => by
    show a * ((if a ≤ v then m else 0) + tailMassNum a rest)
       ≤ (if a ≤ v then m * v else 0) + tailMomentNum a rest
    rw [Nat.mul_add]
    refine Nat.add_le_add ?_ (markov_inequality a rest)
    rcases Nat.lt_or_ge v a with h | h
    · -- v < a, so ¬ a ≤ v
      rw [if_neg (Nat.not_le_of_gt h), if_neg (Nat.not_le_of_gt h),
          Nat.mul_zero]
      exact Nat.le_refl 0
    · -- a ≤ v
      rw [if_pos h, if_pos h, Nat.mul_comm a m]
      exact Nat.mul_le_mul_left m h

end E213.Lib.Math.Probability.Markov
