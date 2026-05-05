import E213.Math.Cohomology.Dyadic.WalkUniversal

import E213.Math.Cohomology.Dyadic.Conjecture
/-!
# Dyadic signature — irrational classifier via K_{3,2}^{(2)} trajectory

User's sharpened claim (G1 §5 follow-up): different irrationals
have distinct K_{3,2}^{(2)} trajectories.  Rational vs irrational
↔ eventually periodic vs aperiodic trajectory; algebraic degree
↔ trajectory complexity; etc.

This file defines a deterministic transition `nextVertex : Fin 5 →
Bool → Fin 5` that depends genuinely on the bit, so the trajectory
is informative.  Each Bool stream gets a *signature*:
  signature bs 0 = ⟨0⟩  (start at S_0)
  signature bs (n+1) = nextVertex (signature bs n) (bs n)
-/

namespace E213.Math.Cohomology.Dyadic.Signature

open E213.Math.Cohomology.Dyadic.Conjecture (periodicBit)

/-- Deterministic vertex transition.  S → T determined by bit.
    T → S cycles through S_0/S_1 from T_0; S_1/S_2 from T_1. -/
def nextVertex (v : Fin 5) (b : Bool) : Fin 5 :=
  match v.val, b with
  | 0, false => ⟨3, by decide⟩  -- S_0 → T_0
  | 0, true  => ⟨4, by decide⟩  -- S_0 → T_1
  | 1, false => ⟨3, by decide⟩  -- S_1 → T_0
  | 1, true  => ⟨4, by decide⟩  -- S_1 → T_1
  | 2, false => ⟨3, by decide⟩  -- S_2 → T_0
  | 2, true  => ⟨4, by decide⟩  -- S_2 → T_1
  | 3, false => ⟨0, by decide⟩  -- T_0 → S_0
  | 3, true  => ⟨1, by decide⟩  -- T_0 → S_1
  | 4, false => ⟨1, by decide⟩  -- T_1 → S_1
  | 4, true  => ⟨2, by decide⟩  -- T_1 → S_2
  | _, _     => ⟨0, by decide⟩  -- unreachable

/-- Signature trajectory: starting at S_0, apply nextVertex bit by bit. -/
def signature (bs : Nat → Bool) : Nat → Fin 5
  | 0 => ⟨0, by decide⟩
  | n + 1 => nextVertex (signature bs n) (bs n)

/-- 1/3 trajectory through step 5: ⟨0,3,1,3,1,3⟩ (period 2 from step 1). -/
theorem one_third_sig :
    signature (periodicBit [false, true]) 4 = ⟨1, by decide⟩
    ∧ signature (periodicBit [false, true]) 9 = ⟨3, by decide⟩ := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- 1/5 trajectory: visits ⟨2⟩ at step 4 (1/3 never does). -/
theorem one_fifth_sig :
    signature (periodicBit [false, false, true, true]) 4 = ⟨2, by decide⟩
    ∧ signature (periodicBit [false, false, true, true]) 9
        = ⟨3, by decide⟩ := by refine ⟨?_, ?_⟩ <;> rfl

/-- 1/7 trajectory: visits ⟨4⟩ at step 9 (1/3 visits ⟨3⟩, 1/5 visits ⟨3⟩). -/
theorem one_seventh_sig :
    signature (periodicBit [false, false, true]) 4 = ⟨1, by decide⟩
    ∧ signature (periodicBit [false, false, true]) 9
        = ⟨4, by decide⟩ := by refine ⟨?_, ?_⟩ <;> rfl

/-- ★ Signature classifier — 1/3, 1/5, 1/7 distinguished. -/
theorem signatures_distinct :
    -- 1/3 vs 1/5: differ at step 4
    signature (periodicBit [false, true]) 4
      ≠ signature (periodicBit [false, false, true, true]) 4
    -- 1/3 vs 1/7: differ at step 9
    ∧ signature (periodicBit [false, true]) 9
        ≠ signature (periodicBit [false, false, true]) 9
    -- 1/5 vs 1/7: differ at step 9
    ∧ signature (periodicBit [false, false, true, true]) 9
        ≠ signature (periodicBit [false, false, true]) 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★ Pointwise-equality lemma — replacement for `funext` in
    contexts where two bit-streams agree pointwise.  Strict-zero
    axiom: structural induction, no propext / no Quot.sound. -/
theorem signature_eq_of_pointwise_eq (bs₁ bs₂ : Nat → Bool)
    (h : ∀ k, bs₁ k = bs₂ k) : ∀ n, signature bs₁ n = signature bs₂ n
  | 0 => rfl
  | n + 1 =>
    show nextVertex (signature bs₁ n) (bs₁ n)
        = nextVertex (signature bs₂ n) (bs₂ n)
    by rw [signature_eq_of_pointwise_eq bs₁ bs₂ h n, h n]

end E213.Math.Cohomology.Dyadic.Signature
