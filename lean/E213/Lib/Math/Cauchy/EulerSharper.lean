import E213.Lib.Math.Cauchy.EulerSeq
import E213.Meta.Tactic.Nat213

/-!
# EulerSharper: e > 5/2 strict bound

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

namespace E213.Lib.Math.Cauchy.EulerSharper

open E213.Theory E213.Lens
open E213.Lib.Math.Cauchy.EulerSeq

/-- **e > 5/2 strict** (n ≥ 3): 2 * eulerNum n ≥ 5 * eulerDen n + 1. -/
theorem euler_sharper_lower (n : Nat) (hn : n ≥ 3) :
    2 * eulerNum n ≥ 5 * eulerDen n + 1 := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      by_cases hk : k = 2
      · subst hk
        show 2 * eulerNum 3 ≥ 5 * eulerDen 3 + 1
        decide
      · have hk3 : k ≥ 3 :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn) (Ne.symm hk)
        have h_inv := ih hk3
        show 2 * eulerNum (k + 1) ≥ 5 * eulerDen (k + 1) + 1
        show 2 * ((k + 1) * eulerNum k + 1) ≥ 5 * ((k + 1) * eulerDen k) + 1
        have h1 : 2 * ((k + 1) * eulerNum k) ≥
                  (k + 1) * (5 * eulerDen k + 1) := by
          have step : 2 * ((k + 1) * eulerNum k) =
                      (k + 1) * (2 * eulerNum k) := by
            rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm 2 (k+1), E213.Tactic.Nat213.mul_assoc]
          rw [step]
          exact Nat.mul_le_mul_left (k+1) h_inv
        have h2 : (k + 1) * (5 * eulerDen k + 1)
                  = 5 * ((k + 1) * eulerDen k) + (k + 1) := by
          rw [Nat.mul_add, Nat.mul_one, ← E213.Tactic.Nat213.mul_assoc,
              Nat.mul_comm (k+1) 5, E213.Tactic.Nat213.mul_assoc]
        -- h1 : (k+1) * (5*eulerDen k + 1) ≤ 2 * ((k+1) * eulerNum k)
        -- h2 says LHS = 5 * ((k+1)*eulerDen k) + (k+1)
        -- Goal: 5 * ((k+1)*eulerDen k) + 1 ≤ 2 * ((k+1)*eulerNum k + 1)
        --                              = 2*(k+1)*eulerNum k + 2
        have h1' : 5 * ((k+1) * eulerDen k) + (k+1) ≤
                   2 * ((k+1) * eulerNum k) := h2 ▸ h1
        have hge2 : 2 ≤ k + 1 :=
          Nat.le_trans (by decide : 2 ≤ 4) (Nat.succ_le_succ hk3)
        -- 5 * X + 1 ≤ 5*X + (k+1) ≤ 2 * Y, want 5*X + 1 ≤ 2*Y + 2
        have : 5 * ((k+1) * eulerDen k) + 1 ≤ 2 * ((k+1) * eulerNum k) :=
          Nat.le_trans (Nat.add_le_add_left
            (Nat.le_trans (by decide : 1 ≤ 2) hge2) _) h1'
        -- Goal: 5 * ((k+1)*eulerDen k) + 1 ≤ 2 * ((k+1)*eulerNum k + 1)
        -- 2 * ((k+1)*eulerNum k + 1) = 2*(k+1)*eulerNum k + 2
        --                            = (2*(k+1)*eulerNum k) + 2
        have hgoal_eq : 2 * ((k+1) * eulerNum k + 1)
                      = 2 * ((k+1) * eulerNum k) + 2 := Nat.mul_add 2 _ 1
        exact hgoal_eq.symm ▸ Nat.le_trans this (Nat.le_add_right _ 2)

end E213.Lib.Math.Cauchy.EulerSharper
