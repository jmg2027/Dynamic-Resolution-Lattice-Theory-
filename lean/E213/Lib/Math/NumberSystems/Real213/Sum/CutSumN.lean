import E213.Meta.Tactic.BoolHelper
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.NumberSystems.Real213.Sum.BoolOrLadder
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset

/-!
# CutSumN: parametric-N cutSum

Generalises `cutSum` from hardcoded factor-2 to parametric `N`.
The original `cutSum` is `cutSumN 2` up to literal/variable
syntax.  Per `theory/essays/bool_assoc_failure_meaning.md`, the
factor-2 hardcode reads only the NT atom of (NS, NT) = (3, 2)
and misses NS; `cutSumN N` lifts this so denominators with `b | N`
close cleanly.

## Key result

`cutSumN_same_denom`: for any `N > 0`, `a, c : Nat`,
  cutSumN N (constCut a N) (constCut c N) ≡ constCut (a + c) N
bidirectionally (cutEq).  The N's cancel: both sides reduce to
`(a+c)·k ≤ N·m`.

## Use

  · `cutSumN 1` : trivial integer case (matches IntValidCut)
  · `cutSumN 2` : dyadic (matches HalfValidCut)
  · `cutSumN 3` : ThirdValidCut anchor — closes b = 3
  · `cutSumN 6` : closes b ∈ {2, 3, 6}, etc.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN

open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)

/-- Parametric bounded-search aux: factor `N` replaces hardcoded 2. -/
def cutSumNAux (N : Nat) (cx cy : Nat → Nat → Bool) (k m1Max : Nat) :
    Nat → Bool
  | 0 => cx 0 (N*k) && cy m1Max (N*k)
  | n+1 => (cx (n+1) (N*k) && cy (m1Max - (n+1)) (N*k))
            || cutSumNAux N cx cy k m1Max n

/-- Parametric cutSum: search range `[0, N*m]` with rate factor `N*k`. -/
def cutSumN (N : Nat) (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  cutSumNAux N cx cy k (N*m) (N*m)

/-- Existential iff for `cutSumNAux`.  Parametric over `N`. -/
theorem cutSumNAux_eq_true_iff (N : Nat) (cx cy : Nat → Nat → Bool)
    (k M : Nat) (n : Nat) :
    cutSumNAux N cx cy k M n = true ↔
    ∃ i, i ≤ n ∧ cx i (N*k) = true ∧ cy (M - i) (N*k) = true :=
  E213.Lib.Math.NumberSystems.Real213.Sum.BoolOrLadder.bool_or_ladder_iff_with_pack
    (fun i => cx i (N*k) && cy (M - i) (N*k))
    (cutSumNAux N cx cy k M)
    (fun _ => E213.Lib.Math.NumberSystems.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _)
    (by show (cx 0 (N*k) && cy M (N*k)) = (cx 0 (N*k) && cy (M - 0) (N*k));
        rw [Nat.sub_zero])
    (fun _ => rfl)
    n

open E213.Tactic.BoolHelper (bool_eq_iff)

/-- ★★★★★ **Key closure: b = N case is bidirectional**.

  For any `N > 0`, `a, c : Nat`:
    cutSumN N (constCut a N) (constCut c N) m k = constCut (a+c) N m k.

  Both sides reduce to `(a+c)·k ≤ N·m` because the N's cancel
  in the existential after dividing through.  Witness: `i = a*k`. -/
theorem cutSumN_same_denom (N a c : Nat) (hN : 0 < N) :
    cutEq (cutSumN N (constCut a N) (constCut c N)) (constCut (a + c) N) := by
  intro m k
  apply bool_eq_iff
  show cutSumNAux N (constCut a N) (constCut c N) k (N*m) (N*m) = true
       ↔ constCut (a + c) N m k = true
  constructor
  · -- forward: witness yields (a+c)*k ≤ N*m
    intro h
    obtain ⟨i, hi, hci, hcsi⟩ :=
      (cutSumNAux_eq_true_iff N (constCut a N) (constCut c N) k (N*m) (N*m)).mp h
    have h_ai : a * (N*k) ≤ N * i := of_decide_eq_true hci
    have h_ci : c * (N*k) ≤ N * (N*m - i) := of_decide_eq_true hcsi
    have h_sum : a * (N*k) + c * (N*k) ≤ N * i + N * (N*m - i) :=
      Nat.add_le_add h_ai h_ci
    have h_add : i + (N*m - i) = N*m :=
      E213.Tactic.NatHelper.add_sub_of_le hi
    have h_ri : N * i + N * (N*m - i) = N * (N*m) := by
      rw [← Nat.mul_add, h_add]
    rw [h_ri] at h_sum
    have h_lhs : a * (N*k) + c * (N*k) = (a+c) * (N*k) :=
      (E213.Tactic.NatHelper.add_mul a c (N*k)).symm
    rw [h_lhs] at h_sum
    have e_lhs : (a+c) * (N*k) = N * ((a+c) * k) := by
      rw [E213.Tactic.NatHelper.mul_left_comm]
    rw [e_lhs] at h_sum
    have h_final : (a+c) * k ≤ N * m :=
      Nat.le_of_mul_le_mul_left h_sum hN
    show decide ((a+c) * k ≤ N * m) = true
    exact decide_eq_true h_final
  · -- backward: witness i = a*k
    intro h
    have h_final : (a+c) * k ≤ N * m := of_decide_eq_true h
    have h_ak_Nm : a*k ≤ N*m := by
      have h1 : a*k ≤ (a+c)*k := by
        rw [E213.Tactic.NatHelper.add_mul]; exact Nat.le_add_right _ _
      exact Nat.le_trans h1 h_final
    refine (cutSumNAux_eq_true_iff N (constCut a N) (constCut c N) k (N*m) (N*m)).mpr
      ⟨a * k, h_ak_Nm, ?_, ?_⟩
    · -- a*(N*k) ≤ N*(a*k): they are equal
      show decide (a * (N*k) ≤ N * (a*k)) = true
      apply decide_eq_true
      have e : a * (N*k) = N * (a*k) := by
        rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e]
      exact Nat.le_refl _
    · -- c*(N*k) ≤ N*(N*m - a*k): divide by N → c*k ≤ N*m - a*k
      show decide (c * (N*k) ≤ N * (N*m - a*k)) = true
      apply decide_eq_true
      have h_ck_sub : c*k ≤ N*m - a*k := by
        have h_swap : c*k + a*k ≤ N*m := by
          rw [Nat.add_comm]
          have e : a*k + c*k = (a+c)*k :=
            (E213.Tactic.NatHelper.add_mul a c k).symm
          rw [e]; exact h_final
        exact E213.Tactic.NatHelper.le_sub_of_add_le h_swap
      have e1 : c * (N*k) = N * (c*k) := by
        rw [E213.Tactic.NatHelper.mul_left_comm]
      rw [e1]
      exact Nat.mul_le_mul_left N h_ck_sub

/-- cutSumN respects cutEq in the left argument.  PURE (no `rw [iff]`). -/
theorem cutSumN_cutEq_left (N : Nat) (cx cx' cy : Nat → Nat → Bool)
    (h : cutEq cx cx') (m k : Nat) :
    cutSumN N cx cy m k = cutSumN N cx' cy m k := by
  apply bool_eq_iff
  show cutSumNAux N cx cy k (N*m) (N*m) = true
       ↔ cutSumNAux N cx' cy k (N*m) (N*m) = true
  constructor
  · intro hh
    obtain ⟨i, hi, hcx, hcy⟩ :=
      (cutSumNAux_eq_true_iff N cx cy k (N*m) (N*m)).mp hh
    exact (cutSumNAux_eq_true_iff N cx' cy k (N*m) (N*m)).mpr
      ⟨i, hi, (h i (N*k)) ▸ hcx, hcy⟩
  · intro hh
    obtain ⟨i, hi, hcx', hcy⟩ :=
      (cutSumNAux_eq_true_iff N cx' cy k (N*m) (N*m)).mp hh
    exact (cutSumNAux_eq_true_iff N cx cy k (N*m) (N*m)).mpr
      ⟨i, hi, (h i (N*k)).symm ▸ hcx', hcy⟩

/-- cutSumN respects cutEq in the right argument.  PURE. -/
theorem cutSumN_cutEq_right (N : Nat) (cx cy cy' : Nat → Nat → Bool)
    (h : cutEq cy cy') (m k : Nat) :
    cutSumN N cx cy m k = cutSumN N cx cy' m k := by
  apply bool_eq_iff
  show cutSumNAux N cx cy k (N*m) (N*m) = true
       ↔ cutSumNAux N cx cy' k (N*m) (N*m) = true
  constructor
  · intro hh
    obtain ⟨i, hi, hcx, hcy⟩ :=
      (cutSumNAux_eq_true_iff N cx cy k (N*m) (N*m)).mp hh
    exact (cutSumNAux_eq_true_iff N cx cy' k (N*m) (N*m)).mpr
      ⟨i, hi, hcx, (h (N*m - i) (N*k)) ▸ hcy⟩
  · intro hh
    obtain ⟨i, hi, hcx, hcy'⟩ :=
      (cutSumNAux_eq_true_iff N cx cy' k (N*m) (N*m)).mp hh
    exact (cutSumNAux_eq_true_iff N cx cy k (N*m) (N*m)).mpr
      ⟨i, hi, hcx, (h (N*m - i) (N*k)).symm ▸ hcy'⟩

end E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
