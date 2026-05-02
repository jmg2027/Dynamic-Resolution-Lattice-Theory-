import E213.Math.Real213.CutMulConstConst
import E213.Math.Real213.CutSumGeneral

/-!
# Real213CutMulConstSum — cutMul·cutSum distributivity (constants, forward)

Closes the F6 doc's open status:
"cutSum × cutMul distributivity (NOT verified)".

## What's now proved (forward direction at constants)

  cutMul (constCut a b) (cutSum (constCut c d) (constCut e d)) m k = true
    ⇒ constCut (a*(c+e)) (b*d) m k = true

This is the **safe direction** of distributivity at constant cuts:
the cut-level product of (a/b) and (c/d + e/d) is bounded by the
algebraic value (a·(c+e))/(b·d).

Equivalently (since a·(c+e) = a·c + a·e):
  cutSum (cutMul (constCut a b) (constCut c d))
         (cutMul (constCut a b) (constCut e d)) m k = true
    ⇒ constCut (a·c + a·e) (b·d) m k = true

Both expressions reach the SAME forward bound — distributivity at
the rational level is preserved by the cut forward direction.
-/

namespace E213.Math.Real213.CutMulConstSum

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul cutMulOuter)
open E213.Math.Real213.CutMulComm (cutMulOuter_eq_true_iff)
open E213.Math.Real213.CutSumTest (constCut)

private theorem mul_4_reassoc_v2 (x y z w : Nat) :
    (x * z) * (y * w) = x * y * (z * w) := by
  rw [Nat.mul_assoc, ← Nat.mul_assoc z y w, Nat.mul_comm z y,
      Nat.mul_assoc y z w, ← Nat.mul_assoc]

/-- ★★★★★★ Generic cutMul forward with rational upper bound on the
    second factor.  If cy m' k' is bounded by constCut C D, and
    cutMul (constCut a b) cy fires at (m, k), then constCut (a·C)(b·D)
    fires at (m, k). -/
theorem cutMul_const_bounded_forward
    (a b C D m k : Nat) (cy : Nat → Nat → Bool)
    (h_cy : ∀ m' k', cy m' k' = true → constCut C D m' k' = true)
    (h : cutMul (constCut a b) cy m k = true) :
    constCut (a * C) (b * D) m k = true := by
  change cutMulOuter (constCut a b) cy k m
        ((m+1)*(k+1)) ((m+1)*(k+1)) = true at h
  rw [cutMulOuter_eq_true_iff] at h
  obtain ⟨m1, _, m2, _, hcx, hcy_at, hmul⟩ := h
  have h_am1 : a * k ≤ b * m1 := of_decide_eq_true hcx
  have h_cy_bound : C * k ≤ D * m2 :=
    of_decide_eq_true (h_cy m2 k hcy_at)
  show decide (a * C * k ≤ b * D * m) = true
  apply decide_eq_true
  -- (a·k)·(C·k) ≤ (b·m1)·(D·m2) = b·D·(m1·m2) ≤ b·D·(m·k) = (b·D·m)·k
  have h_prod : (a * k) * (C * k) ≤ (b * m1) * (D * m2) :=
    Nat.mul_le_mul h_am1 h_cy_bound
  have h_lhs : (a * k) * (C * k) = (a * C * k) * k := by
    rw [mul_4_reassoc_v2 a C k k, ← Nat.mul_assoc]
  have h_rhs : (b * m1) * (D * m2) = (b * D) * (m1 * m2) :=
    mul_4_reassoc_v2 b D m1 m2
  rw [h_lhs, h_rhs] at h_prod
  have h_step : (b * D) * (m1 * m2) ≤ (b * D) * (m * k) :=
    Nat.mul_le_mul_left _ hmul
  have h_combine : (a * C * k) * k ≤ (b * D * m) * k := by
    rw [show (b * D * m) * k = (b * D) * (m * k) from Nat.mul_assoc _ _ _]
    exact Nat.le_trans h_prod h_step
  cases k with
  | zero => simp
  | succ j =>
    rw [Nat.mul_comm (a * C * (j + 1)) (j + 1),
        Nat.mul_comm (b * D * m) (j + 1)] at h_combine
    exact Nat.le_of_mul_le_mul_left h_combine (Nat.succ_pos j)

/-- ★★★★★★★ Distributivity forward at constants:
    cutMul (a/b) (cutSum (c/d) (e/d)) = true ⇒ constCut (a·(c+e), b·d) = true.

  Proof: cutSum_same_denom_forward bounds the inner cutSum by
  constCut(c+e, d).  Then cutMul_const_bounded_forward applies. -/
theorem cutMul_const_distrib_forward
    (a b c d e m k : Nat)
    (h : cutMul (constCut a b)
                (cutSum (constCut c d) (constCut e d)) m k = true) :
    constCut (a * (c + e)) (b * d) m k = true := by
  have h_inner_bound : ∀ m' k', cutSum (constCut c d) (constCut e d) m' k' = true
                              → constCut (c + e) d m' k' = true :=
    fun m' k' => cutSum_same_denom_forward c d e m' k'
  exact cutMul_const_bounded_forward a b (c + e) d m k _ h_inner_bound h

end E213.Math.Real213.CutMulConstSum
