import E213.Meta.Tactic.BoolHelper
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN

/-!
# CutSumNMixed: cross-denominator closure for cutSumN

Extends `cutSumN_same_denom` to mixed denominators when both divide N:

  cutSumN_mixed_denom: for `b₁·q₁ = N` and `b₂·q₂ = N`,
    cutSumN N (constCut a b₁) (constCut c b₂) ≡ constCut (a·q₁ + c·q₂) N.

## Reading

The N's still cancel because every term has N = b_i · q_i in the
right place.  Both sides reduce to `(a·q₁ + c·q₂)·k ≤ N·m`.

## Examples

  · `N = 6, b₁ = 2, b₂ = 3, q₁ = 3, q₂ = 2`:
      cutSumN 6 (a/2) (c/3) ≡ (3a + 2c)/6
  · `N = 12, b₁ = 4, b₂ = 6, q₁ = 3, q₂ = 2`:
      cutSumN 12 (a/4) (c/6) ≡ (3a + 2c)/12
  · `N = 5, b₁ = b₂ = 5, q₁ = q₂ = 1`:
      cutSumN 5 (a/5) (c/5) ≡ (a + c)/5  [= cutSumN_same_denom 5]

## (3, 2) atomic reading

Per `theory/essays/methodology/bool_assoc_failure_meaning.md`, this closes the
ALGEBRAIC closure of cutSumN over ALL (b₁, b₂) where lcm divides
some reachable N.  For b ∈ ⟨2, 3⟩^mult (multiplicative monoid of
{2, 3}), N = lcm(b₁, b₂) is always reachable, giving full algebra.
For b = 5, 7, 11 (outside ⟨2, 3⟩^mult), `cutSumN b` gives
per-fiber self-closure but cross-fiber sums need separate N
choices.  Every such b is still derived from (3, 2) additively
(`Theory/Atomicity/Five.lean atomic_iff_five` for 5 etc.).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Sum.CutSumNMixed

open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
  (cutSumN cutSumNAux cutSumNAux_eq_true_iff)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)

open E213.Tactic.BoolHelper (bool_eq_iff)

/-- ★★★★★ **Mixed-denominator closure for cutSumN**.

  For `b₁ · q₁ = N` and `b₂ · q₂ = N` (i.e., both b's divide N):
    cutSumN N (constCut a b₁) (constCut c b₂) m k
      = constCut (a*q₁ + c*q₂) N m k.

  Both sides reduce to `(a*q₁ + c*q₂)*k ≤ N*m`.  The N's cancel
  by substituting `N = b_i * q_i` and dividing through by `b_i`. -/
theorem cutSumN_mixed_denom (N b₁ b₂ q₁ q₂ a c : Nat)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h₁ : b₁ * q₁ = N) (h₂ : b₂ * q₂ = N) :
    cutEq (cutSumN N (constCut a b₁) (constCut c b₂))
          (constCut (a * q₁ + c * q₂) N) := by
  intro m k
  apply bool_eq_iff
  show cutSumNAux N (constCut a b₁) (constCut c b₂) k (N*m) (N*m) = true
       ↔ constCut (a * q₁ + c * q₂) N m k = true
  constructor
  · intro h
    obtain ⟨i, hi, hci, hcsi⟩ :=
      (cutSumNAux_eq_true_iff N (constCut a b₁) (constCut c b₂) k (N*m) (N*m)).mp h
    have h_ai : a * (N*k) ≤ b₁ * i := of_decide_eq_true hci
    have h_ci : c * (N*k) ≤ b₂ * (N*m - i) := of_decide_eq_true hcsi
    -- Rewrite a*(N*k) = a*(b₁*q₁*k) = b₁*(a*q₁*k)
    have e_aNk : a * (N*k) = b₁ * (a * q₁ * k) := by
      rw [show N = b₁ * q₁ from h₁.symm]
      rw [show b₁ * q₁ * k = b₁ * (q₁ * k) from
            E213.Tactic.NatHelper.mul_assoc b₁ q₁ k]
      rw [show a * (b₁ * (q₁ * k)) = b₁ * (a * (q₁ * k)) from
            E213.Tactic.NatHelper.mul_left_comm a b₁ (q₁ * k)]
      rw [E213.Tactic.NatHelper.mul_assoc a q₁ k]
    rw [e_aNk] at h_ai
    have h_aq1k : a * q₁ * k ≤ i :=
      Nat.le_of_mul_le_mul_left h_ai hb₁
    have e_cNk : c * (N*k) = b₂ * (c * q₂ * k) := by
      rw [show N = b₂ * q₂ from h₂.symm]
      rw [show b₂ * q₂ * k = b₂ * (q₂ * k) from
            E213.Tactic.NatHelper.mul_assoc b₂ q₂ k]
      rw [show c * (b₂ * (q₂ * k)) = b₂ * (c * (q₂ * k)) from
            E213.Tactic.NatHelper.mul_left_comm c b₂ (q₂ * k)]
      rw [E213.Tactic.NatHelper.mul_assoc c q₂ k]
    rw [e_cNk] at h_ci
    have h_cq2k : c * q₂ * k ≤ N*m - i :=
      Nat.le_of_mul_le_mul_left h_ci hb₂
    have h_add : i + (N*m - i) = N*m :=
      E213.Tactic.NatHelper.add_sub_of_le hi
    have h_sum : a * q₁ * k + c * q₂ * k ≤ N * m := by
      calc a * q₁ * k + c * q₂ * k
          ≤ i + (N*m - i) := Nat.add_le_add h_aq1k h_cq2k
        _ = N * m := h_add
    have e_lhs : a * q₁ * k + c * q₂ * k = (a * q₁ + c * q₂) * k :=
      (E213.Tactic.NatHelper.add_mul (a*q₁) (c*q₂) k).symm
    rw [e_lhs] at h_sum
    show decide ((a * q₁ + c * q₂) * k ≤ N * m) = true
    exact decide_eq_true h_sum
  · intro h
    have h_final : (a * q₁ + c * q₂) * k ≤ N * m := of_decide_eq_true h
    -- Witness i = a * q₁ * k
    have h_aq1k_Nm : a * q₁ * k ≤ N * m := by
      have h1 : a * q₁ * k ≤ (a * q₁ + c * q₂) * k := by
        rw [E213.Tactic.NatHelper.add_mul]; exact Nat.le_add_right _ _
      exact Nat.le_trans h1 h_final
    refine (cutSumNAux_eq_true_iff N (constCut a b₁) (constCut c b₂) k (N*m) (N*m)).mpr
      ⟨a * q₁ * k, h_aq1k_Nm, ?_, ?_⟩
    · -- a*(N*k) ≤ b₁*(a*q₁*k):  equal, since both = b₁*a*q₁*k
      show decide (a * (N*k) ≤ b₁ * (a * q₁ * k)) = true
      apply decide_eq_true
      have e_aNk : a * (N*k) = b₁ * (a * q₁ * k) := by
        rw [show N = b₁ * q₁ from h₁.symm]
        rw [show b₁ * q₁ * k = b₁ * (q₁ * k) from
              E213.Tactic.NatHelper.mul_assoc b₁ q₁ k]
        rw [show a * (b₁ * (q₁ * k)) = b₁ * (a * (q₁ * k)) from
              E213.Tactic.NatHelper.mul_left_comm a b₁ (q₁ * k)]
        rw [E213.Tactic.NatHelper.mul_assoc a q₁ k]
      rw [e_aNk]
      exact Nat.le_refl _
    · -- c*(N*k) ≤ b₂*(N*m - a*q₁*k)
      show decide (c * (N*k) ≤ b₂ * (N*m - a * q₁ * k)) = true
      apply decide_eq_true
      -- c*q₂*k ≤ N*m - a*q₁*k (from a*q₁*k + c*q₂*k ≤ N*m)
      have h_cq2k_sub : c * q₂ * k ≤ N * m - a * q₁ * k := by
        have h_swap : c * q₂ * k + a * q₁ * k ≤ N * m := by
          rw [Nat.add_comm]
          have e : a * q₁ * k + c * q₂ * k = (a * q₁ + c * q₂) * k :=
            (E213.Tactic.NatHelper.add_mul (a*q₁) (c*q₂) k).symm
          rw [e]; exact h_final
        exact E213.Tactic.NatHelper.le_sub_of_add_le h_swap
      -- c*(N*k) = b₂*(c*q₂*k)
      have e_cNk : c * (N*k) = b₂ * (c * q₂ * k) := by
        rw [show N = b₂ * q₂ from h₂.symm]
        rw [show b₂ * q₂ * k = b₂ * (q₂ * k) from
              E213.Tactic.NatHelper.mul_assoc b₂ q₂ k]
        rw [show c * (b₂ * (q₂ * k)) = b₂ * (c * (q₂ * k)) from
              E213.Tactic.NatHelper.mul_left_comm c b₂ (q₂ * k)]
        rw [E213.Tactic.NatHelper.mul_assoc c q₂ k]
      rw [e_cNk]
      exact Nat.mul_le_mul_left b₂ h_cq2k_sub

/-! ## §2 — Sanity examples -/

/-- 6-denominator: cutSumN 6 (a/2) (c/3) = (3a + 2c)/6. -/
theorem cutSumN_six_2_3 (a c : Nat) :
    cutEq (cutSumN 6 (constCut a 2) (constCut c 3))
          (constCut (a * 3 + c * 2) 6) :=
  cutSumN_mixed_denom 6 2 3 3 2 a c
    (by decide) (by decide) (by decide) (by decide)

/-- Concrete: 1/2 + 1/3 = 5/6 (via cutSumN 6). -/
theorem cutSumN_six_half_third :
    cutEq (cutSumN 6 (constCut 1 2) (constCut 1 3))
          (constCut 5 6) := by
  have h := cutSumN_six_2_3 1 1
  -- 1*3 + 1*2 = 5
  have e : 1 * 3 + 1 * 2 = 5 := by decide
  rw [e] at h
  exact h

end E213.Lib.Math.NumberSystems.Real213.Sum.CutSumNMixed
