import E213.Kernel.Tactic.Nat213
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest

/-!
# CutSumComm: cutSum commutativity (real proof)

Strategy: prove iff existential, then bijection j = M - i.
-/

namespace E213.Math.Real213.CutSumComm

open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Firmware E213.Hypervisor

/-- cutSumAux is true iff an existential witness exists. -/
theorem cutSumAux_eq_true_iff (cx cy : Nat → Nat → Bool) (k M : Nat) (n : Nat) :
    cutSumAux cx cy k M n = true ↔
    ∃ i, i ≤ n ∧ cx i (2*k) = true ∧ cy (M - i) (2*k) = true := by
  induction n with
  | zero =>
    constructor
    · intro h
      refine ⟨0, Nat.le_refl _, ?_, ?_⟩
      · cases hcx : cx 0 (2*k) with
        | true => rfl
        | false =>
          have : (cx 0 (2*k) && cy M (2*k)) = true := h
          rw [hcx] at this; cases this
      · rw [Nat.sub_zero]
        cases hcy : cy M (2*k) with
        | true => rfl
        | false =>
          have : (cx 0 (2*k) && cy M (2*k)) = true := h
          cases hcx : cx 0 (2*k) <;> rw [hcx, hcy] at this <;> cases this
    · rintro ⟨i, hi, hcx, hcy⟩
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      rw [Nat.sub_zero] at hcy
      show (cx 0 (2*k) && cy M (2*k)) = true
      rw [hcx, hcy]; rfl
  | succ j ih =>
    constructor
    · intro h
      have h' : ((cx (j+1) (2*k) && cy (M - (j+1)) (2*k))
                  || cutSumAux cx cy k M j) = true := h
      cases hfirst : (cx (j+1) (2*k) && cy (M - (j+1)) (2*k)) with
      | true =>
        refine ⟨j+1, Nat.le_refl _, ?_, ?_⟩
        · cases hcx : cx (j+1) (2*k) with
          | true => rfl
          | false =>
            cases hcy : cy (M - (j+1)) (2*k) <;>
              rw [hcx, hcy] at hfirst <;> cases hfirst
        · cases hcy : cy (M - (j+1)) (2*k) with
          | true => rfl
          | false =>
            cases hcx : cx (j+1) (2*k) <;>
              rw [hcx, hcy] at hfirst <;> cases hfirst
      | false =>
        rw [hfirst] at h'
        have h'' : cutSumAux cx cy k M j = true := by
          cases hrec : cutSumAux cx cy k M j with
          | true => rfl
          | false => rw [hrec] at h'; cases h'
        obtain ⟨i, hi, hcx, hcy⟩ := (ih).mp h''
        exact ⟨i, Nat.le_succ_of_le hi, hcx, hcy⟩
    · rintro ⟨i, hi, hcx, hcy⟩
      show ((cx (j+1) (2*k) && cy (M - (j+1)) (2*k))
              || cutSumAux cx cy k M j) = true
      by_cases hij : i = j+1
      · subst hij
        rw [hcx, hcy]; rfl
      · have hi' : i ≤ j := by
          rcases Nat.lt_or_ge i (j+1) with h_lt | h_ge
          · exact Nat.lt_succ_iff.mp h_lt
          · exact absurd (Nat.le_antisymm hi h_ge) hij
        have rec_true : cutSumAux cx cy k M j = true :=
          (ih).mpr ⟨i, hi', hcx, hcy⟩
        rw [rec_true]
        cases (cx (j+1) (2*k) && cy (M - (j+1)) (2*k)) <;> rfl

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSum (cutSum cutSumAux)

private theorem bool_eq_of_iff_true (a b : Bool)
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **cutSum commutativity** — via iff existential + bijection.  PURE. -/
theorem cutSum_comm (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutSum cx cy m k = cutSum cy cx m k := by
  apply bool_eq_of_iff_true
  refine Iff.trans (cutSumAux_eq_true_iff cx cy k (2*m) (2*m))
    (Iff.trans ?_ (cutSumAux_eq_true_iff cy cx k (2*m) (2*m)).symm)
  constructor
  · rintro ⟨i, hi, hcx, hcy⟩
    refine ⟨2*m - i, Nat.sub_le _ _, ?_, ?_⟩
    · exact hcy
    · rw [E213.Tactic.Nat213.sub_sub_self hi]; exact hcx
  · rintro ⟨j, hj, hcy, hcx⟩
    refine ⟨2*m - j, Nat.sub_le _ _, ?_, ?_⟩
    · exact hcx
    · rw [E213.Tactic.Nat213.sub_sub_self hj]; exact hcy

/-- cutSum monotone in cy: cy implies cy' → cutSum cx cy implies cutSum cx cy'. -/
theorem cutSum_mono_right (cx cy cy' : Nat → Nat → Bool)
    (h : ∀ m' k', cy m' k' = true → cy' m' k' = true)
    (m k : Nat) :
    cutSum cx cy m k = true → cutSum cx cy' m k = true := by
  intro hsum
  have h_inner : cutSumAux cx cy k (2*m) (2*m) = true := hsum
  obtain ⟨i, hi, hcx, hcy⟩ :=
    (cutSumAux_eq_true_iff cx cy k (2*m) (2*m)).mp h_inner
  show cutSumAux cx cy' k (2*m) (2*m) = true
  exact (cutSumAux_eq_true_iff cx cy' k (2*m) (2*m)).mpr
    ⟨i, hi, hcx, h (2*m - i) (2*k) hcy⟩

/-- cutSum monotone in cx: symmetric via cutSum_comm. -/
theorem cutSum_mono_left (cx cx' cy : Nat → Nat → Bool)
    (h : ∀ m' k', cx m' k' = true → cx' m' k' = true)
    (m k : Nat) :
    cutSum cx cy m k = true → cutSum cx' cy m k = true := by
  intro hsum
  rw [cutSum_comm] at hsum
  have := cutSum_mono_right cy cx cx' h m k hsum
  rw [cutSum_comm]
  exact this

end E213.Math.Real213.CutSumComm
