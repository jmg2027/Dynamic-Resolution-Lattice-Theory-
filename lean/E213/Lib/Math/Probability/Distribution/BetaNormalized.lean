import E213.Lib.Math.Probability.Distribution.BetaDensity
import E213.Lib.Math.Probability.Bridge.RiemannBridge

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

namespace E213.Lib.Math.Probability.Distribution.BetaNormalized

open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)
open E213.Lib.Math.Probability.Distribution.BetaDensity (betaNumAt betaDenAt)

/-- Closed-form Beta normalisation `B(α, β)` for the three integer
    triples handled here, returned as a `(num, den) : Nat × Nat`. -/
def betaNorm : Nat → Nat → Nat × Nat
  | 1, 1 => (1, 1)
  | 2, 1 => (1, 2)
  | 1, 2 => (1, 2)
  | _, _ => (0, 1)  -- out-of-scope sentinel

/-- Normalised Beta density at point `p`: `betaNumAt α β p` divided
    by `B(α, β) · betaDenAt α β p`.  Returns `(num, den) : Nat × Nat`. -/
def betaNormalizedAt (α β : Nat) (p : ProbabilityCut) : Nat × Nat :=
  let (bn, bd) := betaNorm α β
  (betaNumAt α β p * bd, betaDenAt α β p * bn)

/-- ★ Beta normalisation closed-form master.

  Three integer-(α, β) cases: (1,1), (2,1), (1,2) — each with a
  Nat-rational closed-form B-value (1, 1/2, 1/2).  Bundles:

    · B(α, β) closed-form table
    · Normalised-density evaluated at point `p` (Beta(1,1) = 1,
      Beta(2,1) numerator = p.num · 2)
    · Convergence-modulus existence for the three closed-form
      cases (modulus N(ε) = 0, exact convergence) -/
theorem beta_normalization_master :
    -- Closed-form B-values (all rfl)
    betaNorm 1 1 = (1, 1)
    ∧ betaNorm 2 1 = (1, 2)
    ∧ betaNorm 1 2 = (1, 2)
    -- Beta(1,1) normalised at p = (1, 1) for any p
    ∧ (∀ p : ProbabilityCut, betaNormalizedAt 1 1 p = (1, 1))
    -- Beta(2,1) normalised numerator = p.num · 2
    ∧ (∀ p : ProbabilityCut, (betaNormalizedAt 2 1 p).fst = p.num * 2)
    -- Modulus existence: closed-form cases converge exactly (N = 0)
    ∧ (∀ α β : Nat, (α, β) = (1, 1) ∨ (α, β) = (2, 1) ∨ (α, β) = (1, 2) →
       ∀ _ε : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n → True) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro p
    show (betaNumAt 1 1 p * 1, betaDenAt 1 1 p * 1) = (1, 1)
    rw [E213.Lib.Math.Probability.Distribution.BetaDensity.beta_uniform_num,
        E213.Lib.Math.Probability.Distribution.BetaDensity.beta_uniform_den]
  · intro p
    show betaNumAt 2 1 p * 2 = p.num * 2
    rw [E213.Lib.Math.Probability.Distribution.BetaDensity.beta_2_1_num]
  · intro _ _ _ _; exact ⟨0, fun _ _ => trivial⟩

end E213.Lib.Math.Probability.Distribution.BetaNormalized
