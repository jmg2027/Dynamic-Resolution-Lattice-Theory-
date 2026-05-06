import E213.Math.NatHelpers.PureNat
import E213.Math.Cauchy.EulerSeq

/-!
# EulerCombinatorialPure: Euler bounds, axiom-free

Rewriting the omega-using inductive bounds of `EulerSeq` with manual
Nat arithmetic.

## Core

`euler_upper_pure`: for every `n`, `3 * eulerDen n ≥ eulerNum n + 1`
(== `S_n < 3 - 1/eulerDen n`).

Inductive step: `(k+1) * (3 * eulerDen k - eulerNum k - 1) ≥ 0`
and `3 * eulerDen (k+1) - eulerNum (k+1) - 1 ≥ ...`.

## Significance

The foundational inequality for *Hermite-style analysis* of the typical
e.  The basis showing the possibility of axiom-free formalization.
-/

namespace E213.Math.Cauchy.EulerCombinatorialPure

open E213.Math.NatHelpers.PureNat
open E213.Math.Cauchy.EulerSeq

/-- **Euler upper bound, axiom-free**: 3 * eulerDen n ≥ eulerNum n + 1.
    No omega — manual Nat reasoning.

    Base cases n=0, n=1 directly by decide.  n=k+1 for k ≥ 1: IH * (k+1)
    + slack chain. -/
theorem euler_upper_pure (n : Nat) : 3 * eulerDen n ≥ eulerNum n + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      match k with
      | 0 => decide  -- n = 1
      | k_pred + 1 =>
          -- k = k_pred + 1 ≥ 1, so (k+1) = k_pred + 2 ≥ 2.
          show 3 * eulerDen (k_pred + 1 + 1) ≥ eulerNum (k_pred + 1 + 1) + 1
          show 3 * ((k_pred + 1 + 1) * eulerDen (k_pred + 1)) ≥
               (k_pred + 1 + 1) * eulerNum (k_pred + 1) + 1 + 1
          have h_assoc : 3 * ((k_pred+1+1) * eulerDen (k_pred+1))
                       = (k_pred+1+1) * (3 * eulerDen (k_pred+1)) := by
            rw [← mul_assoc, Nat.mul_comm 3 (k_pred+1+1), mul_assoc]
          rw [h_assoc]
          have h_mul : (k_pred+1+1) * (3 * eulerDen (k_pred+1)) ≥
                       (k_pred+1+1) * (eulerNum (k_pred+1) + 1) :=
            Nat.mul_le_mul_left (k_pred+1+1) ih
          have h_distrib : (k_pred+1+1) * (eulerNum (k_pred+1) + 1)
                         = (k_pred+1+1) * eulerNum (k_pred+1) + (k_pred+1+1) := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [h_distrib] at h_mul
          have h_ge_2 : k_pred + 1 + 1 ≥ 2 :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          have h_target : (k_pred+1+1) * eulerNum (k_pred+1) + (k_pred+1+1) ≥
                          (k_pred+1+1) * eulerNum (k_pred+1) + 1 + 1 := by
            rw [Nat.add_assoc]
            exact Nat.add_le_add_left h_ge_2 _
          exact Nat.le_trans h_target h_mul

/-- **Euler lower bound, axiom-free**: n ≥ 2 → eulerNum n ≥ 2 * eulerDen n + 1.
    (S_n > 2 strict for n ≥ 2.) -/
theorem euler_lower_pure (n : Nat) (hn : n ≥ 2) :
    eulerNum n ≥ 2 * eulerDen n + 1 := by
  induction n with
  | zero =>
      exfalso; exact Nat.not_succ_le_zero 1 hn
  | succ k ih =>
      match k with
      | 0 =>
          exfalso
          have : 1 ≤ 0 := Nat.le_of_succ_le_succ hn
          exact Nat.not_succ_le_zero 0 this
      | 1 =>
          decide
      | k_pred + 2 =>
          have hk2 : k_pred + 2 ≥ 2 :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          have h_inv := ih hk2
          show eulerNum (k_pred + 2 + 1) ≥ 2 * eulerDen (k_pred + 2 + 1) + 1
          show (k_pred+2+1) * eulerNum (k_pred+2) + 1 ≥
               2 * ((k_pred+2+1) * eulerDen (k_pred+2)) + 1
          have h_assoc : 2 * ((k_pred+2+1) * eulerDen (k_pred+2))
                       = (k_pred+2+1) * (2 * eulerDen (k_pred+2)) := by
            rw [← mul_assoc, Nat.mul_comm 2 (k_pred+2+1), mul_assoc]
          rw [h_assoc]
          have h_mul : (k_pred+2+1) * eulerNum (k_pred+2) ≥
                       (k_pred+2+1) * (2 * eulerDen (k_pred+2) + 1) :=
            Nat.mul_le_mul_left (k_pred+2+1) h_inv
          have h_distrib : (k_pred+2+1) * (2 * eulerDen (k_pred+2) + 1)
                         = (k_pred+2+1) * (2 * eulerDen (k_pred+2)) + (k_pred+2+1) := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [h_distrib] at h_mul
          -- h_mul : (k+1) * eulerNum k ≥ (k+1) * (2 * eulerDen k) + (k+1)
          -- Drop the +(k+1) → ≥ (k+1) * (2 * eulerDen k)
          have h_drop : (k_pred+2+1) * (2 * eulerDen (k_pred+2)) + (k_pred+2+1) ≥
                        (k_pred+2+1) * (2 * eulerDen (k_pred+2)) :=
            Nat.le_add_right _ _
          have h_chain : (k_pred+2+1) * eulerNum (k_pred+2) ≥
                         (k_pred+2+1) * (2 * eulerDen (k_pred+2)) :=
            Nat.le_trans h_drop h_mul
          exact Nat.add_le_add_right h_chain 1

/-- **Combinatorial Hermite-direction**: 2 < S_n < 3 strict for n ≥ 2.
    The *first integer constraint* on e — no a/b fits this cut
    (mod-2 form of e ≠ a/b for b ≥ 1).

    Specifically: `2 * eulerDen n < eulerNum n` AND `3 * eulerDen n
    > eulerNum n` for n ≥ 2.  Hence S_n ∈ (2, 3) strict. -/
theorem euler_in_open_2_3 (n : Nat) (hn : n ≥ 2) :
    2 * eulerDen n < eulerNum n ∧ eulerNum n < 3 * eulerDen n := by
  refine ⟨?_, ?_⟩
  · -- 2 * eulerDen n < eulerNum n.  From euler_lower: eulerNum ≥ 2*eulerDen + 1.
    have := euler_lower_pure n hn
    exact Nat.lt_of_succ_le this
  · -- eulerNum n < 3 * eulerDen n.  From euler_upper: 3*eulerDen ≥ eulerNum + 1.
    have := euler_upper_pure n
    exact Nat.lt_of_succ_le this

end E213.Math.Cauchy.EulerCombinatorialPure
