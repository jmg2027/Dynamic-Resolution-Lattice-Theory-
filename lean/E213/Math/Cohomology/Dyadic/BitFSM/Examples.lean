import E213.Math.Cohomology.Dyadic.BitFSM.Bound
import E213.Math.Cohomology.Dyadic.TierBridge

/-!
# Concrete BitFSM examples — Tier 0 (rationals)

Validates the BitFSM framework with explicit constructions:

  - 1/3 = .010101...   ↔ BitFSM(2)
  - 1/5 = .001100110011... ↔ BitFSM(4)
  - 1/7 = .001001001... ↔ BitFSM(3)

For each, the BitFSM is a "shift register" cycling through the
period.  Shows Tier 0 ⊂ BitFSM-class with explicit state count
= dyadic period.
-/

namespace E213.Math.Cohomology.Dyadic.BitFSM.Examples

/-- BitFSM for 1/3 (period 2): 2-state cycle. -/
def fsm_one_third : BitFSM 2 where
  init := ⟨0, by decide⟩
  step v := match v with
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨0, by decide⟩
  out v := v.val == 1

/-- BitFSM for 1/5 (period 4): 4-state cycle.
    Pattern: state 0 → bit 0; 1 → bit 0; 2 → bit 1; 3 → bit 1. -/
def fsm_one_fifth : BitFSM 4 where
  init := ⟨0, by decide⟩
  step v := match v with
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨2, by decide⟩
    | ⟨2, _⟩ => ⟨3, by decide⟩
    | ⟨3, _⟩ => ⟨0, by decide⟩
  out v := v.val ≥ 2

/-- BitFSM for 1/7 (period 3): 3-state cycle. -/
def fsm_one_seventh : BitFSM 3 where
  init := ⟨0, by decide⟩
  step v := match v with
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨2, by decide⟩
    | ⟨2, _⟩ => ⟨0, by decide⟩
  out v := v.val == 2

/-- 1/3 BitFSM produces the expected bits. -/
theorem fsm_one_third_bits :
    fsm_one_third.bits 0 = false
    ∧ fsm_one_third.bits 1 = true
    ∧ fsm_one_third.bits 2 = false
    ∧ fsm_one_third.bits 3 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- 1/5 BitFSM produces the expected period-4 bits [F, F, T, T]. -/
theorem fsm_one_fifth_bits :
    fsm_one_fifth.bits 0 = false ∧ fsm_one_fifth.bits 1 = false
    ∧ fsm_one_fifth.bits 2 = true ∧ fsm_one_fifth.bits 3 = true
    ∧ fsm_one_fifth.bits 4 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- 1/7 BitFSM produces the expected period-3 bits [F, F, T]. -/
theorem fsm_one_seventh_bits :
    fsm_one_seventh.bits 0 = false ∧ fsm_one_seventh.bits 1 = false
    ∧ fsm_one_seventh.bits 2 = true
    ∧ fsm_one_seventh.bits 3 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- ★★★ Tier 0 ⊂ BitFSM (concrete witnesses): 1/3, 1/5, 1/7 each
    have explicit BitFSM with state count = dyadic period. -/
theorem tier0_bitfsm_witnesses :
    (∃ m : BitFSM 2, m.bits 0 = false ∧ m.bits 1 = true)
    ∧ (∃ m : BitFSM 4, m.bits 2 = true ∧ m.bits 3 = true)
    ∧ (∃ m : BitFSM 3, m.bits 0 = false ∧ m.bits 2 = true) :=
  ⟨⟨fsm_one_third, by decide, by decide⟩,
   ⟨fsm_one_fifth, by decide, by decide⟩,
   ⟨fsm_one_seventh, by decide, by decide⟩⟩

/-- fsm_one_third's run state matches k % 2 (Nat-level). -/
theorem fsm_one_third_run_val (k : Nat) :
    (fsm_one_third.run k).val = k % 2 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show (fsm_one_third.step (fsm_one_third.run k')).val = (k' + 1) % 2
    have h_val_lt : (fsm_one_third.run k').val < 2 :=
      (fsm_one_third.run k').isLt
    rcases Nat.lt_or_ge (fsm_one_third.run k').val 1 with h0 | h1
    · -- val = 0
      have hval : (fsm_one_third.run k').val = 0 := by omega
      have hrun : fsm_one_third.run k' = ⟨0, by decide⟩ := Fin.ext hval
      rw [hrun]; show 1 = (k' + 1) % 2
      rw [hval] at ih; omega
    · -- val = 1
      have hval : (fsm_one_third.run k').val = 1 := by omega
      have hrun : fsm_one_third.run k' = ⟨1, by decide⟩ := Fin.ext hval
      rw [hrun]; show 0 = (k' + 1) % 2
      rw [hval] at ih; omega

/-- ★★★★★ fsm_one_third generates exactly the bit13 pattern. -/
theorem fsm_one_third_eq_bit13 (k : Nat) :
    fsm_one_third.bits k = bit13 k := by
  show ((fsm_one_third.run k).val == 1) = (k % 2 == 1)
  rw [fsm_one_third_run_val]

end E213.Math.Cohomology.Dyadic.BitFSM.Examples
