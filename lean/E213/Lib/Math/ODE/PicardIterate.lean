import E213.Meta.Tactic.NatHelper

/-!
# Differential Equations 213 — Picard iteration (atomic, Nat-discrete)

213-native paradigm: an ODE `y' = f(y)` with initial condition
`y(0) = y0` is solved by *iteration*, not by an existence theorem
chasing analytic-completeness.  At the discrete (Nat-time) level
the iterate is purely combinatorial.

Atomic content:
  * `picardIterate y0 f n` — `n` iterates of the discrete map
    `y_{k+1} = y_k + f(y_k)`.
  * Constant `f := fun _ => c` collapses to `y0 + n · c`.
  * Identity `f := fun y => y` collapses to `y0 · 2^n`.
-/

namespace E213.Lib.Math.ODE.PicardIterate

/-- **Picard iteration** at the discrete `Nat` level: starting at
    `y0`, apply `step y := y + f y` `n` times. -/
def picardIterate (y0 : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => y0
  | n + 1 => picardIterate y0 f n + f (picardIterate y0 f n)

/-- ★ Iterate at 0 = `y0` (rfl). -/
theorem picard_zero (y0 : Nat) (f : Nat → Nat) :
    picardIterate y0 f 0 = y0 := rfl

/-- ★ Iterate at 1 = `y0 + f y0` (rfl). -/
theorem picard_one (y0 : Nat) (f : Nat → Nat) :
    picardIterate y0 f 1 = y0 + f y0 := rfl

/-- The *constant* RHS `f := fun _ => c`. -/
def constRHS (c : Nat) : Nat → Nat := fun _ => c

/-- ★ Constant RHS collapses to `y0 + n · c` (linear growth). -/
theorem picard_const (y0 c : Nat) : ∀ n,
    picardIterate y0 (constRHS c) n = y0 + n * c
  | 0 => by
      show y0 = y0 + 0 * c
      rw [Nat.zero_mul, Nat.add_zero]
  | n + 1 => by
      show picardIterate y0 (constRHS c) n + c = y0 + (n + 1) * c
      rw [picard_const y0 c n]
      show (y0 + n * c) + c = y0 + (n + 1) * c
      rw [Nat.add_assoc, Nat.succ_mul]

/-- The *exponential* RHS `f := fun y => y` (so `y_{k+1} = 2 y_k`). -/
def expRHS : Nat → Nat := fun y => y

/-- Term-mode helper: `a + a = a * 2`. -/
theorem add_self_eq_mul_two (a : Nat) : a + a = a * 2 := by
  show a + a = a * (1 + 1)
  rw [Nat.mul_add, Nat.mul_one]

/-- ★ Exponential RHS collapses to `y0 · 2^n`. -/
theorem picard_exp (y0 : Nat) : ∀ n,
    picardIterate y0 expRHS n = y0 * 2 ^ n
  | 0 => by
      show y0 = y0 * 2 ^ 0
      show y0 = y0 * 1
      exact (Nat.mul_one y0).symm
  | n + 1 => by
      show picardIterate y0 expRHS n + picardIterate y0 expRHS n
            = y0 * 2 ^ (n + 1)
      rw [picard_exp y0 n]
      show y0 * 2 ^ n + y0 * 2 ^ n = y0 * 2 ^ (n + 1)
      rw [add_self_eq_mul_two (y0 * 2 ^ n)]
      show (y0 * 2 ^ n) * 2 = y0 * 2 ^ (n + 1)
      rw [E213.Tactic.NatHelper.mul_assoc y0 (2 ^ n) 2]
      show y0 * (2 ^ n * 2) = y0 * 2 ^ (n + 1)
      rfl

end E213.Lib.Math.ODE.PicardIterate
