import E213.Lib.Physics.Foundations.AtomicConstantsParametric

/-!
# Atomic Constants Parametric Uniqueness — n = 3 (C2 Step 5)

Step 5 of conjecture C2 (Atomic constants uniqueness).

At fixed `n = 3` the C2b equation `(m²−1)(n²−1) = (m+n)²−1`
becomes `(m²−1)·8 = (m+3)²−1`, simplifying to
  `7·m² − 6·m − 16 = 0`.
Discriminant `36 + 4·7·16 = 484 = 22²`, so `m = (6 ± 22) / 14`,
giving the unique Nat solution **m = 2** (= NT).

This file mirrors `AtomicConstantsParametric.lean` (n=2 case),
swapping in the analogous Nat-monotonicity chain for `n = 3`.

STRICT ∅-AXIOM (no `omega`, no Mathlib).
-/

namespace E213.Lib.Physics.Foundations.AtomicConstantsParametricN3

open E213.Lib.Physics.Foundations.AtomicConstantsUnique
open E213.Lib.Physics.Foundations.AtomicConstantsParametric (sq_of_add)
open E213.Tactic.Nat213 (add_mul mul_assoc mul_sub_distrib sub_one_add_one
  sub_add_cancel le_sub_of_add_le add_sub_cancel_right)

/-! ## §1 — `7·m² > 6m + 17` for `m ≥ 3` -/

/-- For m ≥ 3, m·m ≥ 3·m. -/
theorem msq_ge_3m (m : Nat) (h : 3 ≤ m) : 3 * m ≤ m * m := by
  rw [Nat.mul_comm 3 m]
  exact Nat.mul_le_mul_left m h

/-- 7·(3·m) = 6m + 15m. -/
theorem seven_three_m (m : Nat) : 7 * (3 * m) = 6 * m + 15 * m := by
  rw [← mul_assoc 7 3 m]
  rw [show (7 : Nat) * 3 = 6 + 15 from rfl]
  rw [add_mul 6 15 m]

/-- For m ≥ 3, 15m > 17. -/
theorem fifteen_m_gt_17 (m : Nat) (h : 3 ≤ m) : 17 < 15 * m := by
  calc 17 < 45 := by decide
    _ = 15 * 3 := rfl
    _ ≤ 15 * m := Nat.mul_le_mul_left 15 h

/-- Core inequality: `6m + 17 < 7·m²` for m ≥ 3.  Pure
    Nat-monotonicity, no `omega`. -/
theorem seven_msq_gt_6m_p17 (m : Nat) (h : 3 ≤ m) :
    6 * m + 17 < 7 * (m * m) := by
  have h1 : 3 * m ≤ m * m := msq_ge_3m m h
  have h2 : 7 * (3 * m) ≤ 7 * (m * m) := Nat.mul_le_mul_left 7 h1
  have h3 : 7 * (3 * m) = 6 * m + 15 * m := seven_three_m m
  have h4 : 17 < 15 * m := fifteen_m_gt_17 m h
  have h5 : 6 * m + 17 < 6 * m + 15 * m := Nat.add_lt_add_left h4 (6 * m)
  rw [← h3] at h5
  exact Nat.lt_of_lt_of_le h5 h2

/-! ## §2 — `(m+3)² + 8 < 8·m²` for `m ≥ 3` -/

/-- `(m + 3)² = m² + 6m + 9`. -/
theorem expand_mp3_sq (m : Nat) :
    (m + 3) * (m + 3) = m * m + 6 * m + 9 := by
  rw [sq_of_add m 3]
  rw [show (3 : Nat) * 3 = 9 from rfl]
  rw [show 2 * (m * 3) = 6 * m from by
    rw [Nat.mul_comm m 3]
    rw [← mul_assoc 2 3 m]]

/-- `8 · m² = m² + 7 · m²`. -/
theorem eight_msq (m : Nat) : 8 * (m * m) = m * m + 7 * (m * m) := by
  show (1 + 7) * (m * m) = m * m + 7 * (m * m)
  rw [add_mul 1 7 (m * m), Nat.one_mul]

/-- For `m ≥ 3`, `(m+3)² + 8 < 8·(m·m)`.  Combines §1 + expansions. -/
theorem mp3_sq_p8_lt_eight_msq (m : Nat) (h : 3 ≤ m) :
    (m + 3) * (m + 3) + 8 < 8 * (m * m) := by
  rw [eight_msq]
  rw [expand_mp3_sq]
  -- goal: m*m + 6*m + 9 + 8 < m*m + 7*(m*m)
  rw [show m * m + 6 * m + 9 + 8 = m * m + (6 * m + 17) from by
    rw [Nat.add_assoc (m*m + 6*m) 9 8]
    rw [Nat.add_assoc (m*m) (6*m) 17]]
  apply Nat.add_lt_add_left
  exact seven_msq_gt_6m_p17 m h

/-! ## §3 — Bridge to `(m+3)² − 1 < (m²−1)·8` -/

/-- For m ≥ 3: `8 · m² = (m² − 1) · 8 + 8`. -/
theorem eight_msq_eq_msub1_mul8_add8 (m : Nat) (h : 3 ≤ m) :
    8 * (m * m) = (m * m - 1) * 8 + 8 := by
  have h1 : 1 ≤ m * m := by
    calc 1 ≤ 3 * 3 := by decide
      _ ≤ m * m := by
          calc 3 * 3 ≤ m * 3 := Nat.mul_le_mul_right 3 h
            _ ≤ m * m := Nat.mul_le_mul_left m h
  have h2 : (m * m - 1) * 8 = 8 * (m * m) - 8 * 1 := by
    rw [Nat.mul_comm (m * m - 1) 8]
    exact mul_sub_distrib h1
  rw [h2, show (8 : Nat) * 1 = 8 from rfl]
  have h3 : 8 ≤ 8 * (m * m) := by
    calc 8 = 8 * 1 := rfl
      _ ≤ 8 * (m * m) := Nat.mul_le_mul_left 8 h1
  exact (sub_add_cancel h3).symm

/-- For m ≥ 3: `(m+3)² − 1 < (m² − 1) · 8`.  Strict gap form. -/
theorem mp3_sq_sub_1_lt_msub1_mul8 (m : Nat) (h : 3 ≤ m) :
    (m + 3) * (m + 3) - 1 < (m * m - 1) * 8 := by
  have ha := mp3_sq_p8_lt_eight_msq m h
  rw [eight_msq_eq_msub1_mul8_add8 m h] at ha
  -- ha : (m+3)² + 8 < (m²-1)·8 + 8, i.e., (m+3)² + 9 ≤ (m²-1)·8 + 8
  have hb : (m + 3) * (m + 3) + 9 ≤ (m * m - 1) * 8 + 8 := ha
  -- Restate as (m+3)² + 1 + 8 ≤ (m²-1)·8 + 8 to apply le_sub_of_add_le
  have hb' : (m + 3) * (m + 3) + 1 + 8 ≤ (m * m - 1) * 8 + 8 := by
    rw [Nat.add_assoc ((m+3)*(m+3)) 1 8]
    exact hb
  have hc : (m + 3) * (m + 3) + 1 ≤ (m * m - 1) * 8 := by
    have := le_sub_of_add_le hb'
    rw [add_sub_cancel_right] at this
    exact this
  -- (m+3)² - 1 < (m+3)² ≤ (m+3)² + 1 ≤ (m²-1)·8
  have h_pos_mp3 : 0 < (m + 3) * (m + 3) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hd : (m + 3) * (m + 3) - 1 < (m + 3) * (m + 3) :=
    Nat.sub_lt h_pos_mp3 (by decide)
  exact Nat.lt_of_lt_of_le hd
    (Nat.le_trans (Nat.le_succ _) hc)

/-! ## §4 — `constraint_C2b m 3 = false` for m ≥ 3 -/

/-- Bool refutation helper: from `a ≠ b` derive `(a == b) = false`. -/
private theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) :
    (a == b) = false := by
  by_cases hab : a = b
  · exact absurd hab h
  · exact decide_eq_false hab

/-- ★★★★★ For all `m ≥ 3`, `constraint_C2b m 3 = false`.
    Fully parametric (∀ m), STRICT ∅-AXIOM. -/
theorem c2b_n3_false_at_ge_3 (m : Nat) (h : 3 ≤ m) :
    constraint_C2b m 3 = false := by
  have hgap := mp3_sq_sub_1_lt_msub1_mul8 m h
  unfold constraint_C2b
  rw [show (3 : Nat) * 3 - 1 = 8 from rfl]
  exact beq_false_of_ne (Nat.ne_of_gt hgap)

/-! ## §5 — Distinct-Nat-literal disequalities, propext-free -/

theorem zero_ne_two : (0 : Nat) ≠ 2 := fun h => Nat.noConfusion h
theorem one_ne_two : (1 : Nat) ≠ 2 :=
  fun h => Nat.noConfusion (Nat.succ.inj h)
theorem three_ne_two : (3 : Nat) ≠ 2 :=
  fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))
theorem succ3_ne_two (k : Nat) : (k + 3) ≠ 2 := fun h =>
  Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))

/-! ## §6 — n=3 parametric uniqueness ∀ m -/

/-- ★★★★★ Parametric n=3 uniqueness (C2 Step 5 master).
    STRICT ∅-AXIOM.
    For all `m : Nat`, `constraint_C2b m 3 = true ↔ m = 2`. -/
theorem c2b_n3_iff_m2 (m : Nat) : constraint_C2b m 3 = true ↔ m = 2 := by
  match m with
  | 0 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Bool.noConfusion (h.symm.trans (rfl : constraint_C2b 0 3 = false))
    · exact absurd h zero_ne_two
  | 1 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Bool.noConfusion (h.symm.trans (rfl : constraint_C2b 1 3 = false))
    · exact absurd h one_ne_two
  | 2 => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | k + 3 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [c2b_n3_false_at_ge_3 (k + 3) (Nat.le_add_left 3 k)] at h
      exact Bool.noConfusion h
    · exact absurd h (succ3_ne_two k)

/-! ## §7 — Master C2 Step 5 -/

/-- ★★★★★ Atomic Constants Step 5 Master.
    Combines Step 4 (n=2 ↔ m=3) and Step 5 (n=3 ↔ m=2) parametric. -/
theorem atomic_constants_parametric_n3_master :
    (∀ m : Nat, constraint_C2b m 3 = true ↔ m = 2)
    ∧ (∀ m : Nat, 3 ≤ m → constraint_C2b m 3 = false)
    ∧ (∀ m : Nat, 3 ≤ m → 6 * m + 17 < 7 * (m * m)) := by
  exact ⟨c2b_n3_iff_m2, c2b_n3_false_at_ge_3, seven_msq_gt_6m_p17⟩

end E213.Lib.Physics.Foundations.AtomicConstantsParametricN3
