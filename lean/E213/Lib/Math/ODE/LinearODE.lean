import E213.Lib.Math.ODE.PicardIterate
import E213.Meta.Tactic.NatHelper

/-!
# Differential Equations 213 — Linear ODE (atomic)

213-native paradigm: a *linear ODE* `y' = a · y` (or `y' = a`) on
the discrete `Nat`-time grid is solved by Picard iteration.  The
solution is a closed-form `Nat` polynomial.

Atomic content:
  * `linearGrowth` — `y' = a` solution: `y(n) = y0 + n · a`.
  * `geometricGrowth` — `y' = y` (Euler-step) solution: `y(n) = y0 · 2^n`.
  * Both are exact at every dyadic time step, no Cauchy-limit
    needed — the discrete dyadic grid IS the trajectory.
-/

namespace E213.Lib.Math.ODE.LinearODE

open E213.Lib.Math.ODE.PicardIterate
  (picardIterate picard_const picard_exp constRHS expRHS)

/-- Linear-growth solution: `y' = constant a`, so the discrete
    iterate at step `n` is `y0 + n · a`. -/
def linearGrowth (y0 a : Nat) (n : Nat) : Nat := y0 + n * a

/-- ★ Linear ODE = Picard with constant RHS. -/
theorem linearODE_eq_picard (y0 a n : Nat) :
    linearGrowth y0 a n = picardIterate y0 (constRHS a) n :=
  (picard_const y0 a n).symm

/-- ★ At `n = 0` returns `y0`. -/
theorem linearGrowth_init (y0 a : Nat) :
    linearGrowth y0 a 0 = y0 := by
  show y0 + 0 * a = y0
  rw [Nat.zero_mul, Nat.add_zero]

/-- Geometric-growth solution: `y' = y` (Euler step), so the
    iterate at step `n` is `y0 · 2^n`. -/
def geometricGrowth (y0 : Nat) (n : Nat) : Nat := y0 * 2 ^ n

/-- ★ Geometric ODE = Picard with identity RHS. -/
theorem geometricODE_eq_picard (y0 n : Nat) :
    geometricGrowth y0 n = picardIterate y0 expRHS n :=
  (picard_exp y0 n).symm

/-- ★ At `n = 0` returns `y0`. -/
theorem geometricGrowth_init (y0 : Nat) :
    geometricGrowth y0 0 = y0 := by
  show y0 * 2 ^ 0 = y0
  show y0 * 1 = y0
  exact Nat.mul_one y0

/-- ★ At `n = 3` returns `y0 · 8`. -/
theorem geometricGrowth_three (y0 : Nat) :
    geometricGrowth y0 3 = y0 * 8 := rfl

end E213.Lib.Math.ODE.LinearODE
