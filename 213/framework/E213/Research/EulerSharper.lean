import E213.Research.EulerSeq

/-!
# Research.EulerSharper: e > 5/2 strict bound

PAPER1 §7.4 의 e > 2 bound 의 sharper version.

## 핵심

`euler_sharper_lower`: `n ≥ 3 → 2 * eulerNum n ≥ 5 * eulerDen n + 1`
즉 `S_n > 5/2` strict for `n ≥ 3`.

Inductive step (Flat-Monomial 없 이): IH 의 differential 이
positive, induction step 가 (n+1) * (positive) + constant ≥ 1.

## 의의

`m/k = 5/2` 에 대해 `orderProj 5 2 (S_n) = false` from `n ≥ 3`
constructive 하 게 close.  (1, 2) ∪ (5/2, 3) cuts 를
이 incremental bound 로 좁힘.
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
