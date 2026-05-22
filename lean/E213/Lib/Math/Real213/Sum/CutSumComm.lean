import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Real213.Sum.BoolOrLadder

/-!
# CutSumComm: cutSum commutativity (real proof)

Strategy: prove iff existential, then bijection j = M - i.
-/

namespace E213.Lib.Math.Real213.Sum.CutSumComm

open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSum (cutSumAux)
open E213.Theory E213.Lens

/-- cutSumAux is true iff an existential witness exists.
    PURE — corollary of `BoolOrLadder.bool_or_ladder_iff` (REAL-2 template). -/
theorem cutSumAux_eq_true_iff (cx cy : Nat → Nat → Bool) (k M : Nat) (n : Nat) :
    cutSumAux cx cy k M n = true ↔
    ∃ i, i ≤ n ∧ cx i (2*k) = true ∧ cy (M - i) (2*k) = true := by
  have iff1 := E213.Lib.Math.Real213.Sum.BoolOrLadder.bool_or_ladder_iff
      (fun i => cx i (2*k) && cy (M - i) (2*k))
      (cutSumAux cx cy k M)
      (by show (cx 0 (2*k) && cy M (2*k)) = (cx 0 (2*k) && cy (M - 0) (2*k));
          rw [Nat.sub_zero])
      (fun _ => rfl)
      n
  constructor
  · intro h
    obtain ⟨i, hi, hand⟩ := iff1.mp h
    obtain ⟨hcx, hcy⟩ :=
      (E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mp hand
    exact ⟨i, hi, hcx, hcy⟩
  · rintro ⟨i, hi, hcx, hcy⟩
    exact iff1.mpr ⟨i, hi,
      (E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mpr ⟨hcx, hcy⟩⟩

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Sum.CutSum (cutSum cutSumAux)

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
    · rw [E213.Tactic.NatHelper.sub_sub_self hi]; exact hcx
  · rintro ⟨j, hj, hcy, hcx⟩
    refine ⟨2*m - j, Nat.sub_le _ _, ?_, ?_⟩
    · exact hcx
    · rw [E213.Tactic.NatHelper.sub_sub_self hj]; exact hcy

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

end E213.Lib.Math.Real213.Sum.CutSumComm
