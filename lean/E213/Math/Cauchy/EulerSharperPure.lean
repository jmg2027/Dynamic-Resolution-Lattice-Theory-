import E213.Math.NatHelpers.PureNat
import E213.Math.Cauchy.EulerSeq
import E213.Math.Cauchy.EulerCombinatorialPure

/-!
# EulerSharperPure: e > 8/3 strict (axiom-free)

`euler_sharper_8_3_pure`: n ≥ 4 → 3 * eulerNum n ≥ 8 * eulerDen n + 1
(== S_n > 8/3 strict).

This sharper bound + e < 3 → e ∈ (8/3, 3).  No integer a/3 in
(8/3, 3) → e ≠ a/3 for any positive integer a.
-/

namespace E213.Math.Cauchy.EulerSharperPure

open E213.Math.NatHelpers.PureNat
open E213.Math.Cauchy.EulerSeq

/-- **e > 8/3 strict** (n ≥ 4): 3 * eulerNum n ≥ 8 * eulerDen n + 1.

    Inductive base n=4: 3·65 = 195 ≥ 193 = 8·24 + 1.
    Step: IH * (k+1) + arithmetic. -/
theorem euler_sharper_8_3_pure (n : Nat) (hn : n ≥ 4) :
    3 * eulerNum n ≥ 8 * eulerDen n + 1 := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      match k with
      | 0 => exact absurd hn (by decide)
      | 1 => exact absurd hn (by decide)
      | 2 => exact absurd hn (by decide)
      | 3 => decide  -- n = 4
      | k_pred + 4 =>
          have hk4 : k_pred + 4 ≥ 4 := Nat.le_add_left 4 k_pred
          have h_inv := ih hk4
          show 3 * ((k_pred + 4 + 1) * eulerNum (k_pred + 4) + 1) ≥
               8 * ((k_pred + 4 + 1) * eulerDen (k_pred + 4)) + 1
          have h_lhs : 3 * ((k_pred+4+1) * eulerNum (k_pred+4) + 1)
                     = (k_pred+4+1) * (3 * eulerNum (k_pred+4)) + 3 := by
            rw [Nat.mul_add, Nat.mul_one, ← mul_assoc,
                Nat.mul_comm 3 (k_pred+4+1), mul_assoc]
          have h_rhs : 8 * ((k_pred+4+1) * eulerDen (k_pred+4)) + 1
                     = (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 1 := by
            rw [← mul_assoc, Nat.mul_comm 8 (k_pred+4+1), mul_assoc]
          rw [h_lhs, h_rhs]
          have h_mul : (k_pred+4+1) * (3 * eulerNum (k_pred+4)) ≥
                       (k_pred+4+1) * (8 * eulerDen (k_pred+4) + 1) :=
            Nat.mul_le_mul_left (k_pred+4+1) h_inv
          have h_dist : (k_pred+4+1) * (8 * eulerDen (k_pred+4) + 1) =
                        (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + (k_pred+4+1) := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [h_dist] at h_mul
          have h_drop : (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + (k_pred+4+1) ≥
                        (k_pred+4+1) * (8 * eulerDen (k_pred+4)) :=
            Nat.le_add_right _ _
          have h_chain : (k_pred+4+1) * (3 * eulerNum (k_pred+4)) ≥
                         (k_pred+4+1) * (8 * eulerDen (k_pred+4)) :=
            Nat.le_trans h_drop h_mul
          have h_add3 : (k_pred+4+1) * (3 * eulerNum (k_pred+4)) + 3 ≥
                        (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 3 :=
            Nat.add_le_add_right h_chain 3
          have h_31 : (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 3 ≥
                      (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 1 := by
            apply Nat.add_le_add_left
            decide
          exact Nat.le_trans h_31 h_add3

/-- eulerDen N ≥ 1, axiom-free version. -/
theorem eulerDen_pos_pure (N : Nat) : eulerDen N ≥ 1 := by
  induction N with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
      show eulerDen (k + 1) ≥ 1
      show (k + 1) * eulerDen k ≥ 1
      have h_kp : k + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_mul : (k + 1) * eulerDen k ≥ (k + 1) * 1 :=
        Nat.mul_le_mul_left (k+1) ih
      rw [Nat.mul_one] at h_mul
      exact Nat.le_trans h_kp h_mul

/-- **e ≠ a/3 (partial sum form, axiom-free)**: for every N ≥ 4
    and positive integer a, `3 · eulerNum N ≠ a · eulerDen N`.

    A statement about the framework's partial sums.  In the limit
    sense S_N → e, this formalizes e ≠ a/3 for any a ∈ ℕ⁺.
    Framework-internal formalization of a Hermite-style proof. -/
theorem e_partial_neq_third_a (a : Nat) (ha : a ≥ 1) (N : Nat) (hN : N ≥ 4) :
    3 * eulerNum N ≠ a * eulerDen N := by
  intro heq
  have h_lower : 3 * eulerNum N ≥ 8 * eulerDen N + 1 :=
    euler_sharper_8_3_pure N hN
  have h_upper : 3 * eulerDen N ≥ eulerNum N + 1 :=
    EulerCombinatorialPure.euler_upper_pure N
  -- From upper: eulerNum N + 1 ≤ 3 * eulerDen N, so eulerNum N ≤ 3 * eulerDen N - 1.
  -- Multiply by 3: 3 * eulerNum N ≤ 9 * eulerDen N - 3.
  have h_upper3 : 3 * eulerNum N + 3 ≤ 9 * eulerDen N := by
    have h1 : 3 * (eulerNum N + 1) ≤ 3 * (3 * eulerDen N) :=
      Nat.mul_le_mul_left 3 h_upper
    have h2 : 3 * (3 * eulerDen N) = 9 * eulerDen N := by
      rw [← mul_assoc]
    rw [h2] at h1
    have h3 : 3 * (eulerNum N + 1) = 3 * eulerNum N + 3 := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h3] at h1
    exact h1
  -- Now: heq : 3 * eulerNum N = a * eulerDen N
  -- h_lower: a * eulerDen N ≥ 8 * eulerDen N + 1
  -- h_upper3: a * eulerDen N + 3 ≤ 9 * eulerDen N
  rw [heq] at h_lower h_upper3
  -- h_lower: a * eulerDen N ≥ 8 * eulerDen N + 1 → a ≥ 9 (if eulerDen N ≥ 1)
  -- h_upper3: a * eulerDen N ≤ 9 * eulerDen N - 3 → a ≤ 8 (similar)
  have hd_pos : eulerDen N ≥ 1 := eulerDen_pos_pure N
  -- From h_lower: a * eulerDen N ≥ 8 * eulerDen N + 1
  -- Suppose a ≤ 8.  Then a * eulerDen N ≤ 8 * eulerDen N.
  -- But ≥ 8 * eulerDen N + 1, contradiction.
  -- So a ≥ 9.
  have h_a_ge_9 : a ≥ 9 := by
    rcases Nat.lt_or_ge a 9 with h_lt | h_ge
    · exfalso
      have h_a_le_8 : a ≤ 8 := Nat.le_of_lt_succ h_lt
      have h_amul : a * eulerDen N ≤ 8 * eulerDen N :=
        Nat.mul_le_mul_right (eulerDen N) h_a_le_8
      have : 8 * eulerDen N + 1 ≤ 8 * eulerDen N :=
        Nat.le_trans h_lower h_amul
      exact Nat.not_succ_le_self (8 * eulerDen N) this
    · exact h_ge
  -- From h_upper3: a * eulerDen N + 3 ≤ 9 * eulerDen N
  -- Suppose a ≥ 9.  Then a * eulerDen N ≥ 9 * eulerDen N.
  -- a * eulerDen N + 3 ≥ 9 * eulerDen N + 3 > 9 * eulerDen N.
  -- Contradicts h_upper3.
  have h_amul9 : a * eulerDen N ≥ 9 * eulerDen N :=
    Nat.mul_le_mul_right (eulerDen N) h_a_ge_9
  have h_plus3 : a * eulerDen N + 3 ≥ 9 * eulerDen N + 3 :=
    Nat.add_le_add_right h_amul9 3
  have : 9 * eulerDen N + 3 ≤ 9 * eulerDen N :=
    Nat.le_trans h_plus3 h_upper3
  -- 9 * eulerDen N + 3 ≤ 9 * eulerDen N means 3 ≤ 0, false.
  have h3le0 : 3 ≤ 0 := Nat.le_of_add_le_add_left this
  exact Nat.not_succ_le_zero 2 h3le0

end E213.Math.Cauchy.EulerSharperPure
