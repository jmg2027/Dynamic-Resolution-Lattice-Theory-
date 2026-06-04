import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Sum.BoolOrLadder
import E213.Meta.Tactic.BoolHelper

/-!
# CutMulComm: cutMul commutativity (real proof)

Strategy: iff existential characterization + bijection (m1, m2) → (m2, m1).

`cutMulInner_eq_true_iff` and `cutMulOuter_eq_true_iff` use the
`BoolOrLadder.bool_or_ladder_iff` template (REAL-1 closure).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mul.CutMulComm

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul cutMulInner cutMulOuter)

open E213.Lib.Math.NumberSystems.Real213.Sum.BoolOrLadder
  (and_eq_true_pure and3_eq_true_pure decide_eq_true_pure
   bool_or_ladder_iff_with_pack)

/-- cutMulInner true iff existential witness on m2.
    PURE — `bool_or_ladder_iff_with_pack` instance over the
    3-conjunct + `decide` Inner predicate. -/
theorem cutMulInner_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m1 : Nat) (n : Nat) :
    cutMulInner cx cy k m m1 n = true ↔
    ∃ m2, m2 ≤ n ∧ cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k :=
  bool_or_ladder_iff_with_pack
    (fun m2 => cx m1 k && cy m2 k && decide (m1 * m2 ≤ m * k))
    (cutMulInner cx cy k m m1)
    (fun _ => Iff.trans (and3_eq_true_pure _ _ _)
      (Iff.intro
        (fun ⟨hcx, hcy, hd⟩ => ⟨hcx, hcy, of_decide_eq_true hd⟩)
        (fun ⟨hcx, hcy, hmul⟩ => ⟨hcx, hcy, decide_eq_true hmul⟩)))
    rfl (fun _ => rfl) n

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul cutMulInner cutMulOuter)

/-- cutMulOuter true iff ∃ m1 ≤ n, ∃ m2 ≤ m2Bound, witnesses.
    PURE — `bool_or_ladder_iff_with_pack` instance composed with
    `cutMulInner_eq_true_iff`. -/
theorem cutMulOuter_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m2Bound : Nat) (n : Nat) :
    cutMulOuter cx cy k m m2Bound n = true ↔
    ∃ m1, m1 ≤ n ∧ ∃ m2, m2 ≤ m2Bound ∧
      cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k :=
  bool_or_ladder_iff_with_pack
    (fun m1 => cutMulInner cx cy k m m1 m2Bound)
    (cutMulOuter cx cy k m m2Bound)
    (fun m1 => cutMulInner_eq_true_iff cx cy k m m1 m2Bound)
    rfl (fun _ => rfl) n

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul cutMulInner cutMulOuter)

open E213.Tactic.BoolHelper (bool_eq_iff)

/-- **cutMul commutativity**: via iff existential + (m1, m2) bijection. -/
theorem cutMul_comm (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutMul cx cy m k = cutMul cy cx m k := by
  apply bool_eq_iff
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

end E213.Lib.Math.NumberSystems.Real213.Mul.CutMulComm
