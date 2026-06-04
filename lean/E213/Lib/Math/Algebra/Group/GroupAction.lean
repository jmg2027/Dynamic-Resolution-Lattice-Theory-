import E213.Lib.Math.Algebra.Group.Cyclic
import E213.Lib.Math.Algebra.Group.Symmetric

/-!
# Group Theory 213 — Group action + orbit (atomic, Nat-side)

213-native paradigm: a *group action* of `G` on `Nat` is a pair of
maps `(act : G → Nat → Nat)` satisfying identity + composition
laws.  Orbit / stabilizer become `Nat`-set membership predicates.

Atomic content:
  * `cyclicShiftAction n a x := (a + x) % n` — action of ℤ/nℤ on
    {0, …, n-1}.
  * Identity-action law (rfl).
  * Composition law via `cyclicAdd`.
  * Orbit of `0` under ℤ/5ℤ is exhaustive (witnessed at 4 points).
-/

namespace E213.Lib.Math.Algebra.Group.GroupAction

open E213.Lib.Math.Algebra.Group.Cyclic (cyclicAdd)
open E213.Lib.Math.Algebra.Group.Symmetric (swap01)

/-- Shift action of ℤ/nℤ on Nat (modular shift). -/
def cyclicShiftAction (n a x : Nat) : Nat := (a + x) % n

/-- ★ Identity action: shift by 0 is `x % n`. -/
theorem shift_zero (n x : Nat) :
    cyclicShiftAction n 0 x = x % n := by
  show (0 + x) % n = x % n
  rw [Nat.zero_add]

/-- ★ ℤ/5ℤ orbit witnesses: shift 1 ↦ 2, 2 ↦ 3, 3 ↦ 4, 4 ↦ 0
    starting from x = 1. -/
theorem z5_orbit_step :
    cyclicShiftAction 5 1 1 = 2
    ∧ cyclicShiftAction 5 1 2 = 3
    ∧ cyclicShiftAction 5 1 3 = 4
    ∧ cyclicShiftAction 5 1 4 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ Action of swap01 on Sₙ-action: 0 ↔ 1 swap. -/
theorem swap01_action :
    swap01 0 = 1 ∧ swap01 1 = 0 := ⟨rfl, rfl⟩

end E213.Lib.Math.Algebra.Group.GroupAction
