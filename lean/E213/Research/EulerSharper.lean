import E213.Research.EulerSeq

/-!
# Research.EulerSharper: e > 5/2 strict bound

A sharper version of the e > 2 bound from PAPER1 §7.4.

## Core

`euler_sharper_lower`: `n ≥ 3 → 2 * eulerNum n ≥ 5 * eulerDen n + 1`
i.e., `S_n > 5/2` strict for `n ≥ 3`.

Inductive step (without Flat-Monomial): the IH's differential is
positive, so the induction step gives (n+1) * (positive) + constant ≥ 1.

## Significance

Constructively closes `orderProj 5 2 (S_n) = false` from `n ≥ 3`
for `m/k = 5/2`.  Narrows the (1, 2) ∪ (5/2, 3) cuts with this
incremental bound.
-/

namespace E213.Research.EulerSharper

open E213.Firmware E213.Hypervisor
open E213.Research.EulerSeq

/-- **e > 5/2 strict** (n ≥ 3): 2 * eulerNum n ≥ 5 * eulerDen n + 1. -/
theorem euler_sharper_lower (n : Nat) (hn : n ≥ 3) :
    2 * eulerNum n ≥ 5 * eulerDen n + 1 := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 2
      · subst hk
        show 2 * eulerNum 3 ≥ 5 * eulerDen 3 + 1
        decide
      · have hk3 : k ≥ 3 := by omega
        have h_inv := ih hk3
        show 2 * eulerNum (k + 1) ≥ 5 * eulerDen (k + 1) + 1
        show 2 * ((k + 1) * eulerNum k + 1) ≥ 5 * ((k + 1) * eulerDen k) + 1
        have h1 : 2 * ((k + 1) * eulerNum k) ≥
                  (k + 1) * (5 * eulerDen k + 1) := by
          have step : 2 * ((k + 1) * eulerNum k) =
                      (k + 1) * (2 * eulerNum k) := by
            rw [← Nat.mul_assoc, Nat.mul_comm 2 (k+1), Nat.mul_assoc]
          rw [step]
          exact Nat.mul_le_mul_left (k+1) h_inv
        have h2 : (k + 1) * (5 * eulerDen k + 1)
                  = 5 * ((k + 1) * eulerDen k) + (k + 1) := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
              Nat.mul_comm (k+1) 5, Nat.mul_assoc]
        rw [h2] at h1
        omega

end E213.Research.EulerSharper
