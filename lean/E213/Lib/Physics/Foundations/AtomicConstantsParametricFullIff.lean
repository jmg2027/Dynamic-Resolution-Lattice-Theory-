import E213.Lib.Physics.Foundations.AtomicConstantsParametricFull

/-!
# Atomic Constants Full Iff (C2 Step 7)

Combines Steps 4-6 into a single full iff:
  ∀ m n : Nat, 2 ≤ m → 2 ≤ n →
    `constraint_C2b m n = true ↔ (m = 3 ∧ n = 2) ∨ (m = 2 ∧ n = 3)`.

Mechanical case analysis on (m, n) — the structural work was
done in Steps 4, 5, 6.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Physics.Foundations.AtomicConstantsParametricFullIff

open E213.Lib.Physics.Foundations.AtomicConstantsUnique
open E213.Lib.Physics.Foundations.AtomicConstantsParametric (c2b_n2_iff_m3
  c2b_n2_false_at_ge_4)
open E213.Lib.Physics.Foundations.AtomicConstantsParametricN3 (c2b_n3_iff_m2
  c2b_n3_false_at_ge_3)
open E213.Lib.Physics.Foundations.AtomicConstantsParametricFull (c2b_sym
  c2b_diag_false)

/-! ## §1 — Distinct-Nat-literal disequalities (propext-free) -/

theorem two_ne_three : (2 : Nat) ≠ 3 :=
  fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))
theorem three_ne_two : (3 : Nat) ≠ 2 :=
  fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))
theorem succ4_ne_three (k : Nat) : (k + 4) ≠ 3 := fun h =>
  Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h)))
theorem succ4_ne_two (k : Nat) : (k + 4) ≠ 2 := fun h =>
  Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))

/-! ## §2 — Full ∀(m, n) iff -/

/-- ★★★★★ Full parametric uniqueness (C2 Step 7).
    For all m, n ≥ 2,
      `constraint_C2b m n = true ↔ (m = 3 ∧ n = 2) ∨ (m = 2 ∧ n = 3)`. -/
theorem c2b_full_iff (m n : Nat) (_hm : 2 ≤ m) (_hn : 2 ≤ n) :
    constraint_C2b m n = true ↔ (m = 3 ∧ n = 2) ∨ (m = 2 ∧ n = 3) := by
  -- Case on n: n = 2 (Step 4), n = 3 (Step 5), n ≥ 4 (need m-case).
  match n, _hn with
  | 2, _ =>
    -- C2b m 2 ↔ m = 3 by Step 4.
    have step4 := c2b_n2_iff_m3 m
    refine ⟨fun h => Or.inl ⟨step4.mp h, rfl⟩, fun h => ?_⟩
    cases h with
    | inl h => exact step4.mpr h.1
    | inr h => exact absurd h.2 two_ne_three
  | 3, _ =>
    -- C2b m 3 ↔ m = 2 by Step 5.
    have step5 := c2b_n3_iff_m2 m
    refine ⟨fun h => Or.inr ⟨step5.mp h, rfl⟩, fun h => ?_⟩
    cases h with
    | inl h => exact absurd h.2 three_ne_two
    | inr h => exact step5.mpr h.1
  | k + 4, _ =>
    -- n = k + 4 ≥ 4. Case on m.
    -- m = 2: by sym + Step 4 (false since k+4 ≠ 3).
    -- m = 3: by sym + Step 5 (false since k+4 ≠ 2).
    -- m ≥ 4: by diagonal (false).
    refine ⟨fun h => ?_, fun h => ?_⟩
    · -- forward: derive contradiction
      exfalso
      match m, _hm with
      | 2, _ =>
        rw [c2b_sym 2 (k + 4)] at h
        rw [c2b_n2_false_at_ge_4 (k + 4) (Nat.le_add_left 4 k)] at h
        exact Bool.noConfusion h
      | 3, _ =>
        rw [c2b_sym 3 (k + 4)] at h
        rw [c2b_n3_false_at_ge_3 (k + 4)
            (Nat.le_trans (by decide) (Nat.le_add_left 4 k))] at h
        exact Bool.noConfusion h
      | k' + 4, _ =>
        rw [c2b_diag_false (k' + 4) (k + 4)
            (Nat.le_trans (by decide) (Nat.le_add_left 4 k'))
            (Nat.le_trans (by decide) (Nat.le_add_left 4 k))] at h
        exact Bool.noConfusion h
    · -- backward: each disjunct contradicts n = k + 4
      cases h with
      | inl h => exact absurd h.2 (succ4_ne_two k)
      | inr h => exact absurd h.2 (succ4_ne_three k)

end E213.Lib.Physics.Foundations.AtomicConstantsParametricFullIff
