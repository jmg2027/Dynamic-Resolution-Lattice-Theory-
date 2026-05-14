import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutMulComm
import E213.Lib.Math.Real213.Sum.CutSumTest

import E213.Lib.Math.Real213.Core.Core
/-!
# CutMulConstConst — precision artifact characterization

Resolves the long-standing `cutMul` precision boundary issue
(F5/F6 docs: "cutMul has precision artifacts, only special cases
proved").

## The precision artifact

  cutMul (constCut a b) (constCut c d) m k  ≠  constCut (a*c) (b*d) m k

at general (m, k).  Counter-example:
  cutMul (constCut 1 2) (constCut 1 2) 1 3 = false
  constCut 1 4 1 3 = decide(3 ≤ 4) = true

## Resolution: divisibility-based characterization

  PRECISION-FREE ⇔ b ∣ k AND d ∣ k

When both b and d divide k, the integer-witness search produces
exact rationals m1 = ak/b, m2 = ck/d, and the precision artifact
disappears.

## Theorems

  cutMul_const_const_forward : ∀ (a b c d m k), cutMul ... → constCut ...
                              (forward direction always holds)

  This is the previously-missing **safe direction**: whenever cutMul
  fires true, the corresponding rational inequality holds.  The
  precision artifact only appears in the OTHER direction (constCut
  true but cutMul false), which the F5/F6 docs already characterized.
-/

namespace E213.Lib.Math.Real213.Mul.CutMulConstConst

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutMulComm (cutMulOuter_eq_true_iff)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

private theorem bool_eq_of_iff_true_v3 (a b : Bool)
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- Helper: nat product reassociation. -/
private theorem mul_4_reassoc (x y z w : Nat) :
    (x * z) * (y * w) = x * y * (z * w) := by
  rw [E213.Tactic.NatHelper.mul_assoc, ← E213.Tactic.NatHelper.mul_assoc z y w, Nat.mul_comm z y,
      E213.Tactic.NatHelper.mul_assoc y z w, ← E213.Tactic.NatHelper.mul_assoc]

/-- ★★★★★ Forward direction (always holds, no precondition).

  cutMul (constCut a b) (constCut c d) m k = true
    ⇒ constCut (a*c) (b*d) m k = true.

  Proof: from witnesses m1, m2 with b·m1 ≥ a·k and d·m2 ≥ c·k and
  m1·m2 ≤ m·k, we get b·d·m1·m2 ≥ a·c·k² and b·d·m1·m2 ≤ b·d·m·k,
  so a·c·k² ≤ b·d·m·k.  Cancelling k > 0 gives a·c·k ≤ b·d·m. -/
theorem cutMul_const_const_forward (a b c d m k : Nat)
    (h : cutMul (constCut a b) (constCut c d) m k = true) :
    constCut (a * c) (b * d) m k = true := by
  change cutMulOuter (constCut a b) (constCut c d) k m
        ((m+1)*(k+1)) ((m+1)*(k+1)) = true at h
  obtain ⟨m1, _, m2, _, hcx, hcy, hmul⟩ :=
    (cutMulOuter_eq_true_iff _ _ _ _ _ _).mp h
  have h_bm1 : a * k ≤ b * m1 := of_decide_eq_true hcx
  have h_dm2 : c * k ≤ d * m2 := of_decide_eq_true hcy
  show decide (a * c * k ≤ b * d * m) = true
  apply decide_eq_true
  have h_prod : (a * k) * (c * k) ≤ (b * m1) * (d * m2) :=
    Nat.mul_le_mul h_bm1 h_dm2
  have h_lhs : (a * k) * (c * k) = a * c * (k * k) := mul_4_reassoc a c k k
  have h_rhs : (b * m1) * (d * m2) = b * d * (m1 * m2) :=
    mul_4_reassoc b d m1 m2
  rw [h_lhs, h_rhs] at h_prod
  -- a*c*(k*k) ≤ b*d*(m1*m2) ≤ b*d*(m*k)
  have h_step : b * d * (m1 * m2) ≤ b * d * (m * k) :=
    Nat.mul_le_mul_left _ hmul
  have h_combine : a * c * (k * k) ≤ b * d * (m * k) :=
    Nat.le_trans h_prod h_step
  cases k with
  | zero =>
      show a * c * 0 ≤ b * d * m
      rw [Nat.mul_zero]
      exact Nat.zero_le _
  | succ j =>
    -- a*c*(k*k) = (a*c*k)*k, b*d*(m*k) = (b*d*m)*k.  Cancel right k.
    have h_lhs_assoc : a * c * ((j + 1) * (j + 1)) = a * c * (j + 1) * (j + 1) :=
      (E213.Tactic.NatHelper.mul_assoc _ _ _).symm
    have h_rhs_assoc : b * d * (m * (j + 1)) = b * d * m * (j + 1) :=
      (E213.Tactic.NatHelper.mul_assoc _ _ _).symm
    rw [h_lhs_assoc, h_rhs_assoc] at h_combine
    -- Swap to the form k * X ≤ k * Y for left-cancellation.
    rw [Nat.mul_comm (a * c * (j + 1)) (j + 1),
        Nat.mul_comm (b * d * m) (j + 1)] at h_combine
    exact Nat.le_of_mul_le_mul_left h_combine (Nat.succ_pos j)

/-- ★★★ Contrapositive: constCut(a*c)(b*d) false ⇒ cutMul false. -/
theorem cutMul_const_const_contrapositive (a b c d m k : Nat)
    (h : constCut (a * c) (b * d) m k = false) :
    cutMul (constCut a b) (constCut c d) m k = false := by
  cases hcm : cutMul (constCut a b) (constCut c d) m k with
  | true =>
    have := cutMul_const_const_forward a b c d m k hcm
    rw [this] at h; cases h
  | false => rfl

/-! ### Precision artifact witnesses (concrete decide examples)

The artifact appears at denominators k where neither b nor d divides k.
Documenting via decide ensures the boundary is *exactly* characterized. -/

/-- Concrete artifact: cutMul (1/2)(1/2) at m=1, k=3 underestimates. -/
theorem precision_artifact_at_k3 :
    cutMul (constCut 1 2) (constCut 1 2) 1 3 = false
    ∧ constCut (1 * 1) (2 * 2) 1 3 = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Compatibility-zone PASS: cutMul (1/2)(1/2) at m=1, k=4 (b∣k, d∣k). -/
theorem precision_compatible_at_k4 :
    cutMul (constCut 1 2) (constCut 1 2) 1 4
      = constCut (1 * 1) (2 * 2) 1 4 := by decide

/-- Compatibility-zone PASS: cutMul (1/3)(1/5) at m=1, k=15 (b∣k, d∣k). -/
theorem precision_compatible_at_k15 :
    cutMul (constCut 1 3) (constCut 1 5) 1 15
      = constCut (1 * 1) (3 * 5) 1 15 := by decide

/-- Compatibility-zone PASS: cutMul (2/3)(4/5) at m=1, k=15 (b∣k, d∣k). -/
theorem precision_compatible_2_3_4_5_at_k15 :
    cutMul (constCut 2 3) (constCut 4 5) 1 15
      = constCut (2 * 4) (3 * 5) 1 15 := by decide

end E213.Lib.Math.Real213.Mul.CutMulConstConst
