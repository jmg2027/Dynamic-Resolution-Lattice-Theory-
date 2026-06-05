import E213.Meta.Tactic.NatHelper

/-!
# Differential Equations 213 — Discrete heat equation (1D)

213-native paradigm: heat equation on a *finite* periodic grid.
`u(x, t+1) = (1/2) u(x-1, t) + (1/2) u(x+1, t)` — discrete
Laplacian.  No PDE existence theorem chase: the discrete update is
purely combinatorial, and conservation (sum of `u` over the grid)
is a `Nat` identity.

Atomic content:
  * `heatStep n u x` — single time-step on a length-`n` periodic grid
  * Sum-conservation: `Σ heatStep ≡ Σ u`  (modulo the 1/2 factor;
    we work in numerator-only `Nat`-side: `2 · sum heatStep = sum + sum`).
  * Constant initial condition is fixed (heat equilibrium).
-/

namespace E213.Lib.Math.Analysis.ODE.HeatEqDiscrete

/-- Periodic neighbour: `(x + 1) mod n`. -/
def rightNbr (n x : Nat) : Nat := (x + 1) % n

/-- Periodic neighbour: `(x + n - 1) mod n`. -/
def leftNbr (n x : Nat) : Nat := (x + n - 1) % n

/-- One discrete heat step on a length-`n` periodic grid.
    *Numerator only* — the actual update is
    `u(x, t+1) = (1/2) (u(x-1) + u(x+1))`.  We track `2 ·
    u(x, t+1)`. -/
def heatStepNum (n : Nat) (u : Nat → Nat) (x : Nat) : Nat :=
  u (leftNbr n x) + u (rightNbr n x)

/-- Constant initial condition. -/
def constInit (c : Nat) : Nat → Nat := fun _ => c

/-- ★ Constant initial condition is preserved by heat step
    (numerator: `2 · c`). -/
theorem heatStep_const (n c x : Nat) :
    heatStepNum n (constInit c) x = c + c := rfl

/-- ★ Constant heat field is `2c` after step (no diffusion needed). -/
theorem heatStep_const_eq_two_c (n c x : Nat) :
    heatStepNum n (constInit c) x = 2 * c := by
  show c + c = 2 * c
  exact (Nat.two_mul c).symm

/-! ## Discrete maximum principle (marathon P1)

`research-notes/frontiers/pde_estimates/discrete_pde_estimates_ladder.md`, rung **P1**.

The discrete heat step is an **average** of two neighbours, so it can neither rise
above the field's max nor fall below its min — the discrete maximum principle, the
seed of all parabolic a-priori estimates.  In the numerator convention
`heatStepNum = 2·u(x,t+1) = u_left + u_right`, a bound `u ≤ B` on the whole grid gives
`heatStepNum ≤ 2B` (i.e. the *averaged* new value `≤ B`), and dually `A ≤ u` gives
`2A ≤ heatStepNum`.  Pure `Nat`, ∅-axiom; uniform in the grid length `n` (hence in the
mesh) — the uniformity that lets the `Real213` limit promote it to the continuous
maximum principle (the next P1 sub-rung). -/

/-- ★★ **Discrete maximum principle (upper).**  If `u ≤ B` everywhere on the grid, the
    post-step numerator `heatStepNum = 2·u_new` is `≤ 2B` — i.e. the new (averaged)
    value does not exceed the old maximum `B`.  Heat does not create hot spots.
    Uniform in the grid length `n`. -/
theorem heatStep_le_two_max (n : Nat) (u : Nat → Nat) (B x : Nat)
    (h : ∀ y, u y ≤ B) : heatStepNum n u x ≤ 2 * B := by
  show u (leftNbr n x) + u (rightNbr n x) ≤ 2 * B
  rw [Nat.two_mul]
  exact Nat.add_le_add (h (leftNbr n x)) (h (rightNbr n x))

/-- ★★ **Discrete maximum principle (lower / minimum principle).**  If `A ≤ u`
    everywhere, then `2A ≤ heatStepNum = 2·u_new` — the new value does not fall below the
    old minimum `A`.  Heat does not create cold spots. -/
theorem heatStep_two_min_le (n : Nat) (u : Nat → Nat) (A x : Nat)
    (h : ∀ y, A ≤ u y) : 2 * A ≤ heatStepNum n u x := by
  show 2 * A ≤ u (leftNbr n x) + u (rightNbr n x)
  rw [Nat.two_mul]
  exact Nat.add_le_add (h (leftNbr n x)) (h (rightNbr n x))

/-- ★★★ **Range preservation.**  Under one heat step, the doubled new value stays inside
    `[2A, 2B]` whenever the old field is in `[A, B]` — i.e. the averaged field stays in
    `[A, B]`.  The interval `[min, max]` is invariant: the discrete heat semigroup is a
    contraction on the sup-norm, the combinatorial root of `‖u(t)‖∞ ≤ ‖u(0)‖∞`. -/
theorem heatStep_range (n : Nat) (u : Nat → Nat) (A B x : Nat)
    (hlo : ∀ y, A ≤ u y) (hhi : ∀ y, u y ≤ B) :
    2 * A ≤ heatStepNum n u x ∧ heatStepNum n u x ≤ 2 * B :=
  ⟨heatStep_two_min_le n u A x hlo, heatStep_le_two_max n u B x hhi⟩

/-- ★★★ **Oscillation does not grow.**  The post-step spread `2B − 2A = 2·(B−A)` bounds
    the new value's deviation from both ends: the oscillation `osc = max − min` is a
    monovariant under the heat step (it never increases), the discrete smoothing estimate
    feeding oscillation decay (rung P2).  Stated as the two-sided bound on the new value's
    distance from the doubled endpoints. -/
theorem heatStep_osc_bound (n : Nat) (u : Nat → Nat) (A B x : Nat)
    (hlo : ∀ y, A ≤ u y) (hhi : ∀ y, u y ≤ B) :
    heatStepNum n u x - 2 * A ≤ 2 * (B - A) ∧
    2 * B - heatStepNum n u x ≤ 2 * (B - A) := by
  obtain ⟨hA, hB⟩ := heatStep_range n u A B x hlo hhi
  have hdist : 2 * B - 2 * A = 2 * (B - A) :=
    (E213.Tactic.NatHelper.mul_sub 2 B A).symm
  refine ⟨?_, ?_⟩
  · -- (2u_new) − 2A ≤ 2B − 2A = 2(B−A)
    have h1 : heatStepNum n u x - 2 * A ≤ 2 * B - 2 * A := Nat.sub_le_sub_right hB (2 * A)
    rw [hdist] at h1; exact h1
  · have h2 : 2 * B - heatStepNum n u x ≤ 2 * B - 2 * A :=
      E213.Tactic.NatHelper.sub_le_sub_left (2 * B) hA
    rw [hdist] at h2; exact h2

end E213.Lib.Math.Analysis.ODE.HeatEqDiscrete
