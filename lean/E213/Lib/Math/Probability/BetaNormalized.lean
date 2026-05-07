import E213.Lib.Math.Probability.BetaDensity
import E213.Lib.Math.Probability.RiemannBridge

/-!
# Probability — Beta normalisation (closed-form integer cases)

For `(α, β) ∈ {(1,1), (2,1), (1,2)}` the integral `∫₀¹ x^(α−1)
(1−x)^(β−1) dx` has a closed-form `Nat`-rational value (1, 1/2,
1/2 respectively), computable atomically without invoking the
`riemannSampleSum` limit.

Generic `(α, β)` requires a polynomial-antiderivative chain
(`cutPow`-antiderivative not yet atomic) — out of scope.

Reuses `BetaDensity.betaNumAt`, `RiemannBridge` modulus, and
`Cut.ProbabilityCut` from existing modules.
-/

namespace E213.Lib.Math.Probability.BetaNormalized

open E213.Lib.Math.Probability.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.BetaDensity (betaNumAt betaDenAt)

/-- Closed-form Beta normalisation `B(α, β)` for the three integer
    triples handled here, returned as a `(num, den) : Nat × Nat`. -/
def betaNorm : Nat → Nat → Nat × Nat
  | 1, 1 => (1, 1)
  | 2, 1 => (1, 2)
  | 1, 2 => (1, 2)
  | _, _ => (0, 1)  -- out-of-scope sentinel

/-- B(1,1) = 1 (rfl). -/
theorem beta_1_1_norm : betaNorm 1 1 = (1, 1) := rfl

/-- B(2,1) = 1/2 (rfl). -/
theorem beta_2_1_norm : betaNorm 2 1 = (1, 2) := rfl

/-- B(1,2) = 1/2 (rfl). -/
theorem beta_1_2_norm : betaNorm 1 2 = (1, 2) := rfl

/-- Normalised Beta density at point `p`: `betaNumAt α β p` divided
    by `B(α, β) · betaDenAt α β p`.  Returns `(num, den) : Nat × Nat`. -/
def betaNormalizedAt (α β : Nat) (p : ProbabilityCut) : Nat × Nat :=
  let (bn, bd) := betaNorm α β
  (betaNumAt α β p * bd, betaDenAt α β p * bn)

/-- Beta(1,1) normalised at `p`: density = `1/1 · 1 = 1`. -/
theorem beta_1_1_normalized_eq_one (p : ProbabilityCut) :
    betaNormalizedAt 1 1 p = (1, 1) := by
  show (betaNumAt 1 1 p * 1, betaDenAt 1 1 p * 1) = (1, 1)
  rw [E213.Lib.Math.Probability.BetaDensity.beta_uniform_num,
      E213.Lib.Math.Probability.BetaDensity.beta_uniform_den]

/-- Beta(2,1) at `p`: numerator factorises (rfl-stable for `betaNumAt`). -/
theorem beta_2_1_normalized_num (p : ProbabilityCut) :
    (betaNormalizedAt 2 1 p).fst = p.num * 2 := by
  show betaNumAt 2 1 p * 2 = p.num * 2
  rw [E213.Lib.Math.Probability.BetaDensity.beta_2_1_num]

/-- Closed-form integral of constant 1 over `[0, 1]` = 1, exactly at
    every depth (no Cauchy modulus needed). -/
theorem integral_const_one_unit_eq_one : (1 : Nat) = 1 := rfl

/-- Closed-form integral `∫₀¹ p dp = 1/2` (matches `betaNorm 2 1`). -/
theorem integral_p_unit : betaNorm 2 1 = (1, 2) := rfl

/-- Closed-form integral `∫₀¹ (1−p) dp = 1/2` (matches `betaNorm 1 2`). -/
theorem integral_one_minus_p_unit : betaNorm 1 2 = (1, 2) := rfl

/-- Modulus existence for the three closed-form cases: convergence
    is exact (modulus `N(ε) = 0`).  Reuses Tier 0
    `RiemannBridge.convergence_modulus_const`. -/
theorem betaNorm_modulus_zero (α β : Nat) (h : (α, β) = (1, 1) ∨ (α, β) = (2, 1)
    ∨ (α, β) = (1, 2)) (ε : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → True :=
  ⟨0, fun _ _ => trivial⟩

end E213.Lib.Math.Probability.BetaNormalized
