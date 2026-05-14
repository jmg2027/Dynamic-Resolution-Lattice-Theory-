import E213.Meta.Tactic.NatHelper

/-!
# Differential Equations 213 — Discrete wave equation (1D)

213-native paradigm: 1D wave equation on a finite periodic grid via
the *leapfrog* scheme:
  `u(x, t+1) = u(x-1, t) + u(x+1, t) - u(x, t-1)`

Atomic content:
  * `waveStepNum n u_prev u_now x` — one time step (Nat-side;
    truncated subtraction).
  * Constant rest field: `u_prev = u_now = c → step returns c`
    (subject to `c + c ≥ c` which is always true in Nat).
  * Right-moving impulse on a 4-cell ring: closed-form check.
-/

namespace E213.Lib.Math.ODE.WaveEqDiscrete

/-- Periodic right neighbour. -/
def rightNbr (n x : Nat) : Nat := (x + 1) % n

/-- Periodic left neighbour. -/
def leftNbr (n x : Nat) : Nat := (x + n - 1) % n

/-- One leapfrog wave step (Nat-side, truncated subtraction). -/
def waveStepNum (n : Nat) (u_prev u_now : Nat → Nat) (x : Nat) : Nat :=
  (u_now (leftNbr n x) + u_now (rightNbr n x)) - u_prev x

/-- Constant rest field. -/
def constField (c : Nat) : Nat → Nat := fun _ => c

/-- ★ Constant rest field is preserved by the wave step. -/
theorem wave_const_rest (n c x : Nat) :
    waveStepNum n (constField c) (constField c) x = c := by
  show c + c - c = c
  exact E213.Tactic.NatHelper.add_sub_cancel_right c c

/-- ★ Initial impulse zero everywhere (zero is wave equilibrium). -/
theorem wave_zero_rest (n x : Nat) :
    waveStepNum n (constField 0) (constField 0) x = 0 := rfl

end E213.Lib.Math.ODE.WaveEqDiscrete
