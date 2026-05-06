import E213.Math.Real213.CutMul

/-!
# Real213CutMulComm: cutMul commutativity (real proof)

Strategy: iff existential characterization + bijection (m1, m2) → (m2, m1).
-/

namespace E213.Math.Real213.CutMulComm

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutMul (cutMul cutMulInner cutMulOuter)

/-- cutMulInner true iff existential witness on m2. -/
theorem cutMulInner_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m1 : Nat) (n : Nat) :
    cutMulInner cx cy k m m1 n = true ↔
    ∃ m2, m2 ≤ n ∧ cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k := by
  induction n with
  | zero =>
    constructor
    · intro h
      have h' : (cx m1 k && cy 0 k && decide (m1 * 0 ≤ m * k)) = true := h
      refine ⟨0, Nat.le_refl _, ?_, ?_, ?_⟩
      · cases hcx : cx m1 k with
        | true => rfl
        | false => rw [hcx] at h'; cases h'
      · cases hcy : cy 0 k with
        | true => rfl
        | false =>
          cases hcx : cx m1 k <;> rw [hcx, hcy] at h' <;> cases h'
      · rw [Nat.mul_zero]; exact Nat.zero_le _
    · rintro ⟨m2, hm2, hcx, hcy, hmul⟩
      have hm2_zero : m2 = 0 := Nat.le_zero.mp hm2
      subst hm2_zero
      show (cx m1 k && cy 0 k && decide (m1 * 0 ≤ m * k)) = true
      rw [hcx, hcy]
      have : decide (m1 * 0 ≤ m * k) = true :=
        decide_eq_true (by rw [Nat.mul_zero]; exact Nat.zero_le _)
      rw [this]; rfl
  | succ j ih =>
    constructor
    · intro h
      have h' : ((cx m1 k && cy (j+1) k && decide (m1 * (j+1) ≤ m * k))
                  || cutMulInner cx cy k m m1 j) = true := h
      cases hfirst : (cx m1 k && cy (j+1) k && decide (m1 * (j+1) ≤ m * k)) with
      | true =>
        refine ⟨j+1, Nat.le_refl _, ?_, ?_, ?_⟩
        · cases hcx : cx m1 k with
          | true => rfl
          | false =>
            cases hcy : cy (j+1) k <;>
              cases hd : decide (m1 * (j+1) ≤ m * k) <;>
              rw [hcx, hcy, hd] at hfirst <;> cases hfirst
        · cases hcy : cy (j+1) k with
          | true => rfl
          | false =>
            cases hcx : cx m1 k <;>
              cases hd : decide (m1 * (j+1) ≤ m * k) <;>
              rw [hcx, hcy, hd] at hfirst <;> cases hfirst
        · cases hd : decide (m1 * (j+1) ≤ m * k) with
          | true => exact of_decide_eq_true hd
          | false =>
            cases hcx : cx m1 k <;>
              cases hcy : cy (j+1) k <;>
              rw [hcx, hcy, hd] at hfirst <;> cases hfirst
      | false =>
        rw [hfirst] at h'
        have h'' : cutMulInner cx cy k m m1 j = true := by
          cases hrec : cutMulInner cx cy k m m1 j with
          | true => rfl
          | false => rw [hrec] at h'; cases h'
        obtain ⟨m2, hm2, hcx, hcy, hmul⟩ := (ih).mp h''
        exact ⟨m2, Nat.le_succ_of_le hm2, hcx, hcy, hmul⟩
    · rintro ⟨m2, hm2, hcx, hcy, hmul⟩
      show ((cx m1 k && cy (j+1) k && decide (m1 * (j+1) ≤ m * k))
              || cutMulInner cx cy k m m1 j) = true
      by_cases hm2_eq : m2 = j+1
      · subst hm2_eq
        rw [hcx, hcy]
        have : decide (m1 * (j+1) ≤ m * k) = true := decide_eq_true hmul
        rw [this]; rfl
      · have hm2' : m2 ≤ j := by
          rcases Nat.lt_or_ge m2 (j+1) with h_lt | h_ge
          · exact Nat.lt_succ_iff.mp h_lt
          · exact absurd (Nat.le_antisymm hm2 h_ge) hm2_eq
        have rec_true : cutMulInner cx cy k m m1 j = true :=
          (ih).mpr ⟨m2, hm2', hcx, hcy, hmul⟩
        rw [rec_true]
        cases (cx m1 k && cy (j+1) k && decide (m1 * (j+1) ≤ m * k)) <;> rfl

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutMul (cutMul cutMulInner cutMulOuter)

/-- cutMulOuter true iff ∃ m1 ≤ n, ∃ m2 ≤ m2Bound, witnesses.
    PURE (∅-axiom): avoids `induction` tactic, `rw [iff]`, and
    `by_cases` to keep `propext` out of the proof body. -/
theorem cutMulOuter_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m2Bound : Nat) :
    ∀ n, cutMulOuter cx cy k m m2Bound n = true ↔
    ∃ m1, m1 ≤ n ∧ ∃ m2, m2 ≤ m2Bound ∧
      cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k
  | 0 => by
    constructor
    · intro h
      have h_inner : cutMulInner cx cy k m 0 m2Bound = true := h
      obtain ⟨m2, hm2, hcx, hcy, hmul⟩ :=
        (cutMulInner_eq_true_iff cx cy k m 0 m2Bound).mp h_inner
      exact ⟨0, Nat.le_refl _, m2, hm2, hcx, hcy, hmul⟩
    · rintro ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩
      have hm1_zero : m1 = 0 := Nat.le_zero.mp hm1
      subst hm1_zero
      show cutMulInner cx cy k m 0 m2Bound = true
      exact (cutMulInner_eq_true_iff cx cy k m 0 m2Bound).mpr
        ⟨m2, hm2, hcx, hcy, hmul⟩
  | j+1 => by
    show (cutMulInner cx cy k m (j+1) m2Bound
            || cutMulOuter cx cy k m m2Bound j) = true ↔ _
    constructor
    · intro h
      cases hfirst : cutMulInner cx cy k m (j+1) m2Bound with
      | true =>
        obtain ⟨m2, hm2, hcx, hcy, hmul⟩ :=
          (cutMulInner_eq_true_iff cx cy k m (j+1) m2Bound).mp hfirst
        exact ⟨j+1, Nat.le_refl _, m2, hm2, hcx, hcy, hmul⟩
      | false =>
        rw [hfirst] at h
        have h' : cutMulOuter cx cy k m m2Bound j = true := by
          cases hrec : cutMulOuter cx cy k m m2Bound j with
          | true => rfl
          | false => rw [hrec] at h; cases h
        obtain ⟨m1, hm1, rest⟩ :=
          (cutMulOuter_eq_true_iff cx cy k m m2Bound j).mp h'
        exact ⟨m1, Nat.le_succ_of_le hm1, rest⟩
    · rintro ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩
      match Nat.decEq m1 (j+1) with
      | isTrue hm1_eq =>
        subst hm1_eq
        have inner_true : cutMulInner cx cy k m (j+1) m2Bound = true :=
          (cutMulInner_eq_true_iff cx cy k m (j+1) m2Bound).mpr
            ⟨m2, hm2, hcx, hcy, hmul⟩
        rw [inner_true]; rfl
      | isFalse hm1_neq =>
        have hm1' : m1 ≤ j :=
          match Nat.lt_or_ge m1 (j+1) with
          | Or.inl h_lt => Nat.lt_succ_iff.mp h_lt
          | Or.inr h_ge => absurd (Nat.le_antisymm hm1 h_ge) hm1_neq
        have outer_true : cutMulOuter cx cy k m m2Bound j = true :=
          (cutMulOuter_eq_true_iff cx cy k m m2Bound j).mpr
            ⟨m1, hm1', m2, hm2, hcx, hcy, hmul⟩
        rw [outer_true]
        cases cutMulInner cx cy k m (j+1) m2Bound <;> rfl

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutMul (cutMul cutMulInner cutMulOuter)

private theorem bool_eq_of_iff_true' (a b : Bool)
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **cutMul commutativity**: via iff existential + (m1, m2) bijection. -/
theorem cutMul_comm (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutMul cx cy m k = cutMul cy cx m k := by
  apply bool_eq_of_iff_true'
  refine Iff.trans (cutMulOuter_eq_true_iff cx cy k m _ _)
    (Iff.trans ?_ (cutMulOuter_eq_true_iff cy cx k m _ _).symm)
  constructor
  · rintro ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩
    refine ⟨m2, hm2, m1, hm1, hcy, hcx, ?_⟩
    rw [Nat.mul_comm]; exact hmul
  · rintro ⟨m1, hm1, m2, hm2, hcy, hcx, hmul⟩
    refine ⟨m2, hm2, m1, hm1, hcx, hcy, ?_⟩
    rw [Nat.mul_comm]; exact hmul

/-- cutMul monotone in cy.  PURE. -/
theorem cutMul_mono_right (cx cy cy' : Nat → Nat → Bool)
    (h : ∀ m' k', cy m' k' = true → cy' m' k' = true)
    (m k : Nat) :
    cutMul cx cy m k = true → cutMul cx cy' m k = true := by
  intro hmul
  have h_inner : cutMulOuter cx cy k m ((m+1)*(k+1)) ((m+1)*(k+1)) = true := hmul
  obtain ⟨m1, hm1, m2, hm2, hcx, hcy, hmuv⟩ :=
    (cutMulOuter_eq_true_iff cx cy k m _ _).mp h_inner
  show cutMulOuter cx cy' k m ((m+1)*(k+1)) ((m+1)*(k+1)) = true
  exact (cutMulOuter_eq_true_iff cx cy' k m _ _).mpr
    ⟨m1, hm1, m2, hm2, hcx, h m2 k hcy, hmuv⟩

/-- cutMul monotone in cx — via cutMul_comm. -/
theorem cutMul_mono_left (cx cx' cy : Nat → Nat → Bool)
    (h : ∀ m' k', cx m' k' = true → cx' m' k' = true)
    (m k : Nat) :
    cutMul cx cy m k = true → cutMul cx' cy m k = true := by
  intro hmul
  rw [cutMul_comm] at hmul
  have := cutMul_mono_right cy cx cx' h m k hmul
  rw [cutMul_comm]
  exact this

end E213.Math.Real213.CutMulComm
