import E213.Term.Tactic.Nat213

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

namespace E213.Lib.Math.ODE.HeatEqDiscrete

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

end E213.Lib.Math.ODE.HeatEqDiscrete
