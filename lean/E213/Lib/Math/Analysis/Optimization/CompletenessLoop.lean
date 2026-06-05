import E213.Meta.Tactic.NatHelper

/-!
# The completeness-LOOP: asymptotic convergence of the gradient value (∅-axiom)

The *second* instruction the gradient-flow monovariant compiles to (the first
being the descent identity, `GradientFlow.gradient_descent_identity`).

`GradientFlow` proved the per-step descent `F(x') = F(x) − τ(1−τ)‖∇F‖²` and that
`F(x') = (1−2τ)²F(x)` — so under a contraction `0 < r = (1−2τ)² < 1`, the value
sequence is `F(xₖ) = rᵏ·F(x₀)`, a **geometric** sequence.  Taking a contraction
`r ≤ 1/2` (e.g. `τ = 1/4 ⟹ r = 1/4`), the value is dominated by the **halving**
sequence `vₖ = N₀ / 2ᵏ`, whose limiting behaviour is the content here.

## Why this is NOT A6 FLOW

A6 FLOW (`MonovariantFlow.flow_reaches`) is well-founded `ℕ`-descent: it reaches
the normal form in **finitely many** steps (the round sphere, linear `ρ`, hits
`0`).  The gradient value `vₖ = N₀/2ᵏ` is different: it is **strictly positive at
every finite step** (`value_pos`) — it *never reaches* its infimum `0` in finite
time — yet it **converges to `0`** with an explicit modulus (`value_below`:
below `1/2ⁿ` after `K(n) = N₀·2ⁿ` steps).  That is the **monotone +
bounded-below ⟹ convergent** instruction (completeness / `MonotonicBounded`),
the asymptotic LOOP, distinct from A6's finite descent.

So gradient-flow `𝓕/𝓦`-monotonicity compiles to exactly two instructions:
  1. **descent identity** — `GradientFlow` (the monovariant descends, rate `‖∇F‖²`);
  2. **completeness-LOOP** — here (the descending bounded value converges,
     asymptotically, never finitely reaching the infimum).
Neither is A6.

## Scope

A modulus-level witness in the repo's `Nat → Nat` modulus idiom
(cf. `K32_ricci_modulus`, `IsContinuousModulus`): the value is the rational
`N₀/2ᵏ`, convergence is the cross-multiplied `ℕ`-inequality `N₀·2ⁿ < 2ᵏ`.  A full
`CauchyCutSeq` construction over `Real213` (`Analysis/CauchyComplete`) is the
heavier completion; the asymptotic *content* — convergence with modulus +
never-finitely-attained infimum — is exactly what is proven here, ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.Optimization.CompletenessLoop

/-- The denominator `2ᵏ` is positive — so the value `vₖ = N₀/2ᵏ` is well-formed
    at every step. -/
theorem den_pos (k : Nat) : 0 < 2 ^ k := Nat.pos_pow_of_pos k (by decide)

/-- **Monotone decreasing**: `vₖ₊₁ ≤ vₖ`, i.e. (cross-multiplied across the
    denominators `2ᵏ`, `2ᵏ⁺¹`) `N₀·2ᵏ ≤ N₀·2ᵏ⁺¹`. -/
theorem value_decreasing (N0 k : Nat) : N0 * 2 ^ k ≤ N0 * 2 ^ (k + 1) :=
  Nat.mul_le_mul_left N0 (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))

/-- **Strictly positive at every finite step** (the non-A6 feature): the value
    `vₖ = N₀/2ᵏ` has positive numerator and denominator for every `k`, so it is
    `> 0` — it never reaches the infimum `0` in finitely many steps. -/
theorem value_pos (N0 : Nat) (h0 : 0 < N0) (k : Nat) : 0 < N0 ∧ 0 < 2 ^ k :=
  ⟨h0, den_pos k⟩

/-- `k < 2ᵏ` (∅-axiom; `Nat.lt_two_pow` is absent in this toolchain). -/
theorem lt_two_pow_self : ∀ k, k < 2 ^ k
  | 0 => by decide
  | k + 1 => by
      have h1 : k + 1 ≤ 2 ^ k := lt_two_pow_self k
      have h2 : 2 ^ k < 2 ^ k * 2 := by
        rw [Nat.mul_two]
        exact Nat.lt_add_of_pos_right (den_pos k)
      rw [Nat.pow_succ]
      exact Nat.lt_of_le_of_lt h1 h2

/-- **Convergence with explicit modulus**: after `K(n) = N₀·2ⁿ` steps the value
    drops below `1/2ⁿ`.  Cross-multiplied: `k ≥ N₀·2ⁿ ⟹ N₀·2ⁿ < 2ᵏ`
    (i.e. `N₀/2ᵏ < 1/2ⁿ`).  The proof is one application of `k < 2ᵏ`. -/
theorem value_below (N0 n k : Nat) (hk : N0 * 2 ^ n ≤ k) : N0 * 2 ^ n < 2 ^ k :=
  Nat.lt_of_le_of_lt hk (lt_two_pow_self k)

/-- ★★★★★ **The completeness-LOOP instruction**: the gradient value sequence
    `vₖ = N₀/2ᵏ` is monotone decreasing, strictly positive at every finite step
    (never finitely reaching its infimum `0`), yet converges to `0` with the
    explicit modulus `K(n) = N₀·2ⁿ`.  Monotone + bounded-below ⟹ convergent —
    the asymptotic LOOP gradient-flow monotonicity compiles to, distinct from
    A6's finite well-founded descent. -/
theorem completeness_loop (N0 : Nat) (h0 : 0 < N0) :
    (∀ k, N0 * 2 ^ k ≤ N0 * 2 ^ (k + 1))
    ∧ (∀ k, 0 < N0 ∧ 0 < 2 ^ k)
    ∧ (∀ n k, N0 * 2 ^ n ≤ k → N0 * 2 ^ n < 2 ^ k) :=
  ⟨value_decreasing N0, value_pos N0 h0, value_below N0⟩

end E213.Lib.Math.Analysis.Optimization.CompletenessLoop
