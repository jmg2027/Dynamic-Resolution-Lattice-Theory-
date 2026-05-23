import E213.Lib.Physics.Foundations.AtomicConstantsUnique
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.Omega213

/-!
# Atomic Constants Parametric Uniqueness (C2 Step 4)

Step 4 of conjecture C2 (Atomic constants uniqueness) per
`research-notes/

## Summary of progress

  Step 1 (`AtomicConstantsUnique.lean`):  bounded uniqueness < 7
  Step 2 (same file):                      factored search bound 100
  Step 3 (same file):                      factored bound 300
  Step 4 (this file):                      single-axis n=2 bound 5000

Single-axis: at fixed `n = 2` (the physical NT) the inner loop
collapses to O(N) so much higher bounds are tractable.  At n = 2
the sole solution is m = 3 (= NS).

Closed-form algebra: at n = 2 the C2b equation reduces to
  `m² = 2m + 3`  ↔  `(m − 3)·(m + 1) = 0`
giving the unique Nat solution m = 3.  A fully parametric (∀ m)
∅-axiom proof requires polynomial manipulation in pure Nat
without `omega` (which leaks propext) or Mathlib `ring`; the
machinery is built up in §1 (`sq_of_add`) for use in Step 5+.

STRICT ∅-AXIOM (Nat213/Omega213 + decide).
-/

namespace E213.Lib.Physics.Foundations.AtomicConstantsParametric

open E213.Lib.Physics.Foundations.AtomicConstantsUnique
open E213.Tactic.NatHelper (add_mul mul_assoc)

/-! ## §1 — Square-of-sum (axiom-free building block) -/

/-- `(x + y) * (x + y) = x*x + 2*(x*y) + y*y`.  Axiom-free analog
    of `Lib/Math/Extras/CauchySchwarz2D.sq_add_two`, inlined to
    avoid the upward dependency. -/
theorem sq_of_add (x y : Nat) :
    (x + y) * (x + y) = x * x + 2 * (x * y) + y * y := by
  rw [Nat.mul_add (x + y) x y, add_mul x y x, add_mul x y y]
  rw [Nat.mul_comm y x]
  rw [← Nat.add_assoc (x * x + x * y) (x * y) (y * y)]
  rw [Nat.add_assoc (x * x) (x * y) (x * y)]
  have h2 : x * y + x * y = 2 * (x * y) := by
    show x * y + x * y = (1 + 1) * (x * y)
    rw [add_mul 1 1 (x * y), Nat.one_mul]
  rw [h2]

/-! ## §2 — `m·m > 2m + 3` for `m ≥ 4` (Nat-monotonicity-only proof) -/

/-- For `m ≥ 4`, `m·m ≥ 4·m`.  Direct from
    `Nat.mul_le_mul_left m : 4 ≤ m → m * 4 ≤ m * m`. -/
theorem msq_ge_4m (m : Nat) (h : 4 ≤ m) : 4 * m ≤ m * m := by
  rw [Nat.mul_comm 4 m]
  exact Nat.mul_le_mul_left m h

/-- For `m ≥ 4`, `4·m = 2m + 2m`.  Decomposes `4` as `2+2`. -/
theorem four_mul_eq_two_add_two (m : Nat) : 4 * m = 2 * m + 2 * m := by
  show 4 * m = 2 * m + 2 * m
  rw [show (4 : Nat) * m = (2 + 2) * m from rfl]
  rw [add_mul 2 2 m]

/-- For `m ≥ 4`, `2·m ≥ 8`. -/
theorem two_m_ge_8 (m : Nat) (h : 4 ≤ m) : 8 ≤ 2 * m := by
  calc 8 = 2 * 4 := rfl
    _ ≤ 2 * m := Nat.mul_le_mul_left 2 h

/-- Core inequality: `m·m > 2·m + 3` for all `m ≥ 4`.  Pure
    Nat-monotonicity argument, no `omega` / `ring`. -/
theorem msq_gt_2m_p3 (m : Nat) (h : 4 ≤ m) : 2 * m + 3 < m * m := by
  have h1 : 4 * m ≤ m * m := msq_ge_4m m h
  have h2 : 4 * m = 2 * m + 2 * m := four_mul_eq_two_add_two m
  have h_2m : 8 ≤ 2 * m := two_m_ge_8 m h
  have h3 : 3 < 2 * m := Nat.lt_of_lt_of_le (by decide : (3 : Nat) < 8) h_2m
  have h4 : 2 * m + 3 < 2 * m + 2 * m := Nat.add_lt_add_left h3 (2 * m)
  rw [← h2] at h4
  exact Nat.lt_of_lt_of_le h4 h1

/-! ## §3 — `(m+2)² + 2 < 3·m²` for `m ≥ 4` (no Nat sub issues) -/

/-- `(m + 2)² = m² + 4m + 4`.  Uses `sq_of_add m 2`. -/
theorem expand_mp2_sq (m : Nat) :
    (m + 2) * (m + 2) = m * m + 4 * m + 4 := by
  rw [sq_of_add m 2]
  rw [show (2 : Nat) * 2 = 4 from rfl]
  rw [show 2 * (m * 2) = 4 * m from by
    rw [Nat.mul_comm m 2]
    rw [← mul_assoc 2 2 m]]

/-- For `m ≥ 4`, `4·m + 8 ≤ 2·(m·m)`.  Doubles `msq_gt_2m_p3`. -/
theorem two_msq_ge_4m_p8 (m : Nat) (h : 4 ≤ m) :
    4 * m + 8 ≤ 2 * (m * m) := by
  have h_le : 2 * m + 4 ≤ m * m := msq_gt_2m_p3 m h
  have h_eq : 4 * m + 8 = 2 * (2 * m + 4) := by
    rw [Nat.mul_add 2 (2 * m) 4]
    rw [show (2 : Nat) * 4 = 8 from rfl]
    rw [← mul_assoc 2 2 m]
  rw [h_eq]
  exact Nat.mul_le_mul_left 2 h_le

/-- `3 · (m·m) = m·m + 2 · (m·m)`. -/
theorem three_msq (m : Nat) : 3 * (m * m) = m * m + 2 * (m * m) := by
  show (1 + 2) * (m * m) = m * m + 2 * (m * m)
  rw [add_mul 1 2 (m * m), Nat.one_mul]

/-- For `m ≥ 4`, `(m+2)² + 2 < 3·(m·m)`.  Combines §2 + §3.
    This is the no-Nat-sub form of `(m+2)² − 1 < (m² − 1)·3`. -/
theorem mp2_sq_p2_lt_three_msq (m : Nat) (h : 4 ≤ m) :
    (m + 2) * (m + 2) + 2 < 3 * (m * m) := by
  rw [three_msq]
  rw [expand_mp2_sq]
  -- goal: m*m + 4*m + 4 + 2 < m*m + 2*(m*m)
  -- simplifies to 4*m + 6 < 2*(m*m), follows from 4*m + 8 ≤ 2*(m*m)
  rw [show m * m + 4 * m + 4 + 2 = m * m + (4 * m + 6) from by
    rw [Nat.add_assoc (m*m + 4*m) 4 2]
    rw [Nat.add_assoc (m*m) (4*m) 6]]
  apply Nat.add_lt_add_left
  -- goal: 4*m + 6 < 2*(m*m)
  exact Nat.lt_of_lt_of_le (by
    show 4 * m + 6 < 4 * m + 8
    exact Nat.add_lt_add_left (by decide : (6 : Nat) < 8) (4 * m))
    (two_msq_ge_4m_p8 m h)

/-! ## §4 — Bridge to `constraint_C2b m 2 = false` -/

open E213.Tactic.NatHelper (mul_sub_distrib sub_one_add_one sub_add_cancel
  le_sub_of_add_le add_sub_cancel_right)

/-- For m ≥ 4: `3 * (m*m) = (m*m - 1) * 3 + 3`. -/
theorem three_msq_eq_msub1_mul3_add3 (m : Nat) (h : 4 ≤ m) :
    3 * (m * m) = (m * m - 1) * 3 + 3 := by
  have h1 : 1 ≤ m * m := by
    calc 1 ≤ 4 * 4 := by decide
      _ ≤ m * m := by
          have h_4_le_m : 4 ≤ m := h
          calc 4 * 4 ≤ m * 4 := Nat.mul_le_mul_right 4 h_4_le_m
            _ ≤ m * m := Nat.mul_le_mul_left m h_4_le_m
  -- (m*m - 1) * 3 = 3 * (m*m) - 3
  have h2 : (m * m - 1) * 3 = 3 * (m * m) - 3 * 1 := by
    rw [Nat.mul_comm (m * m - 1) 3]
    exact mul_sub_distrib h1
  rw [h2, show (3 : Nat) * 1 = 3 from rfl]
  -- 3 * (m * m) = (3 * (m * m) - 3) + 3
  -- by add_sub_of_le since 3 ≤ 3*(m*m)
  have h3 : 3 ≤ 3 * (m * m) := by
    calc 3 = 3 * 1 := rfl
      _ ≤ 3 * (m * m) := Nat.mul_le_mul_left 3 h1
  exact (sub_add_cancel h3).symm

/-- For m ≥ 4: `(m+2)*(m+2) - 1 < (m*m - 1) * 3`.  Strict gap form. -/
theorem mp2_sq_sub_1_lt_msub1_mul3 (m : Nat) (h : 4 ≤ m) :
    (m + 2) * (m + 2) - 1 < (m * m - 1) * 3 := by
  -- Step a: (m+2)² + 2 < 3*(m*m) [from §3]
  have ha := mp2_sq_p2_lt_three_msq m h
  -- Step b: rewrite 3*(m*m) = (m*m - 1)*3 + 3
  rw [three_msq_eq_msub1_mul3_add3 m h] at ha
  -- ha : (m+2)*(m+2) + 2 < (m*m - 1)*3 + 3
  -- Step c: (m+2)² + 3 ≤ (m*m - 1)*3 + 3, then strip the +3 via le_sub_of_add_le
  have hb : (m + 2) * (m + 2) + 3 ≤ (m * m - 1) * 3 + 3 := ha
  have hc : (m + 2) * (m + 2) ≤ (m * m - 1) * 3 := by
    have := le_sub_of_add_le hb
    -- this : (m+2)*(m+2) ≤ (m*m - 1)*3 + 3 - 3
    rw [add_sub_cancel_right] at this
    exact this
  -- Step d: (m+2)² - 1 < (m+2)² (since (m+2)² > 0)
  have hd : (m + 2) * (m + 2) - 1 < (m + 2) * (m + 2) := by
    apply Nat.sub_lt
    · -- 0 < (m+2)*(m+2)
      have : 0 < m + 2 := Nat.succ_pos _
      exact Nat.mul_pos this this
    · decide
  -- Step e: combine
  exact Nat.lt_of_lt_of_le hd hc

/-- Helper: from `a ≠ b` for Nat derive `(a == b) = false`. -/
theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) :
    (a == b) = false := by
  by_cases hab : a = b
  · exact absurd hab h
  · exact decide_eq_false hab

/-- ★★★★★ For all `m ≥ 4`, `constraint_C2b m 2 = false`.
    Fully parametric (∀ m), STRICT ∅-AXIOM. -/
theorem c2b_n2_false_at_ge_4 (m : Nat) (h : 4 ≤ m) :
    constraint_C2b m 2 = false := by
  have hgap := mp2_sq_sub_1_lt_msub1_mul3 m h
  unfold constraint_C2b
  rw [show (2 : Nat) * 2 - 1 = 3 from rfl]
  exact beq_false_of_ne (Nat.ne_of_gt hgap)

/-! ## §5 — Parametric n=2 uniqueness ∀ m -/

/-- Witnesses that distinct Nat literals are unequal, propext-free. -/
theorem zero_ne_three : (0 : Nat) ≠ 3 := fun h => Nat.noConfusion h
theorem one_ne_three : (1 : Nat) ≠ 3 := fun h => Nat.noConfusion (Nat.succ.inj h)
theorem two_ne_three : (2 : Nat) ≠ 3 :=
  fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))
theorem succ4_ne_three (k : Nat) : (k + 4) ≠ 3 := fun h =>
  Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h)))

/-- ★★★★★ Parametric n=2 uniqueness (C2 Step 4 master).
    STRICT ∅-AXIOM.
    For all `m : Nat`, `constraint_C2b m 2 = true ↔ m = 3`. -/
theorem c2b_n2_iff_m3 (m : Nat) : constraint_C2b m 2 = true ↔ m = 3 := by
  match m with
  | 0 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Bool.noConfusion (h.symm.trans (rfl : constraint_C2b 0 2 = false))
    · exact absurd h zero_ne_three
  | 1 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Bool.noConfusion (h.symm.trans (rfl : constraint_C2b 1 2 = false))
    · exact absurd h one_ne_three
  | 2 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Bool.noConfusion (h.symm.trans (rfl : constraint_C2b 2 2 = false))
    · exact absurd h two_ne_three
  | 3 => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | k + 4 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [c2b_n2_false_at_ge_4 (k + 4) (Nat.le_add_left 4 k)] at h
      exact Bool.noConfusion h
    · exact absurd h (succ4_ne_three k)

/-! ## §6 — Master C2 Step 4 theorem -/

/-- ★★★★★ Atomic Constants Parametric Master (C2 Step 4).
    STRICT ∅-AXIOM.

    Step 4 closes the n=2 column of C2b PARAMETRICALLY (∀ m : Nat).

    Bundles:
      (i)   `c2b_n2_iff_m3` — ∀ m, C2b m 2 = true ↔ m = 3
      (ii)  `c2b_n2_false_at_ge_4` — ∀ m ≥ 4, C2b m 2 = false
      (iii) `mp2_sq_sub_1_lt_msub1_mul3` — strict gap

    Built from `msq_gt_2m_p3 : m·m > 2m + 3 (m ≥ 4)` via Nat
    monotonicity (`Nat.mul_le_mul_left/right`) — pure 213-native
    arithmetic, no `omega`, no `ring`, no Mathlib. -/
theorem atomic_constants_parametric_master :
    (∀ m : Nat, constraint_C2b m 2 = true ↔ m = 3)
    ∧ (∀ m : Nat, 4 ≤ m → constraint_C2b m 2 = false)
    ∧ (∀ m : Nat, 4 ≤ m → 2 * m + 3 < m * m) := by
  exact ⟨c2b_n2_iff_m3, c2b_n2_false_at_ge_4, msq_gt_2m_p3⟩

end E213.Lib.Physics.Foundations.AtomicConstantsParametric
