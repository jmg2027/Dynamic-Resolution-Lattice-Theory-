import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.BoolOrLadder

/-!
# CutMulComm: cutMul commutativity (real proof)

Strategy: iff existential characterization + bijection (m1, m2) → (m2, m1).

`cutMulInner_eq_true_iff` and `cutMulOuter_eq_true_iff` use the
`BoolOrLadder.bool_or_ladder_iff` template (REAL-1 closure).
-/

namespace E213.Lib.Math.Real213.Mul.CutMulComm

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulInner cutMulOuter)

/-- cutMulInner true iff existential witness on m2.
    PURE — corollary of `BoolOrLadder.bool_or_ladder_iff` (REAL-1 template). -/
theorem cutMulInner_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m1 : Nat) (n : Nat) :
    cutMulInner cx cy k m m1 n = true ↔
    ∃ m2, m2 ≤ n ∧ cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k := by
  have iff1 := E213.Lib.Math.Real213.Sum.BoolOrLadder.bool_or_ladder_iff
      (fun m2 => cx m1 k && cy m2 k && decide (m1 * m2 ≤ m * k))
      (cutMulInner cx cy k m m1)
      (rfl) (fun _ => rfl) n
  constructor
  · intro h
    obtain ⟨m2, hm2, hand⟩ := iff1.mp h
    obtain ⟨h12, hd⟩ :=
      (E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mp hand
    obtain ⟨hcx, hcy⟩ :=
      (E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mp h12
    exact ⟨m2, hm2, hcx, hcy, of_decide_eq_true hd⟩
  · rintro ⟨m2, hm2, hcx, hcy, hmul⟩
    refine iff1.mpr ⟨m2, hm2, ?_⟩
    exact (E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mpr
      ⟨(E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mpr ⟨hcx, hcy⟩,
       decide_eq_true hmul⟩

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulInner cutMulOuter)

/-- cutMulOuter true iff ∃ m1 ≤ n, ∃ m2 ≤ m2Bound, witnesses.
    PURE — corollary of `BoolOrLadder.bool_or_ladder_iff` composed with
    `cutMulInner_eq_true_iff` (REAL-1 template). -/
theorem cutMulOuter_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m2Bound : Nat) (n : Nat) :
    cutMulOuter cx cy k m m2Bound n = true ↔
    ∃ m1, m1 ≤ n ∧ ∃ m2, m2 ≤ m2Bound ∧
      cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k := by
  have iff1 := E213.Lib.Math.Real213.Sum.BoolOrLadder.bool_or_ladder_iff
      (fun m1 => cutMulInner cx cy k m m1 m2Bound)
      (cutMulOuter cx cy k m m2Bound)
      (rfl) (fun _ => rfl) n
  constructor
  · intro h
    obtain ⟨m1, hm1, hinner⟩ := iff1.mp h
    obtain ⟨m2, hm2, hcx, hcy, hmul⟩ :=
      (cutMulInner_eq_true_iff cx cy k m m1 m2Bound).mp hinner
    exact ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩
  · rintro ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩
    refine iff1.mpr ⟨m1, hm1, ?_⟩
    exact (cutMulInner_eq_true_iff cx cy k m m1 m2Bound).mpr
      ⟨m2, hm2, hcx, hcy, hmul⟩

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulInner cutMulOuter)

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

end E213.Lib.Math.Real213.Mul.CutMulComm
