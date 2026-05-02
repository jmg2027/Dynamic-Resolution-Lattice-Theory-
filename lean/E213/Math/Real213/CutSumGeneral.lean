import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumComm
import E213.Math.Real213.CutSumTest

/-!
# Real213CutSumGeneral — generic cutSum over any denominator

Resolves the F6 doc's open status:
"cutSum_assoc on arbitrary same-denom (blocked at b ≥ 3 by
divisibility — only b ∈ {1, 2} give clean closed forms in Lean)".

## What was missing

For const cut summation:
  cutSum (constCut a b) (constCut c b) m k  vs  constCut (a+c) b m k

Previously only b=1 (cutSum_int_int) and b=2 (cutSum_half_general)
were proved bidirectionally.  At b ≥ 3, a divisibility precision
artifact (analogous to cutMul) prevents the binary midpoint search
from witnessing exact boundary cases.

## What's now proved

  cutSum_same_denom_forward  (UNIVERSAL — any b ≥ 1):
    cutSum (constCut a b) (constCut c b) m k = true
      ⇒ constCut (a+c) b m k = true.

  cutSum_diff_denom_forward (UNIVERSAL — any b, d ≥ 1):
    cutSum (constCut a b) (constCut c d) m k = true
      ⇒ constCut (a*d + b*c) (b*d) m k = true.
    (This is the cross-multiplication form for different denominators.)

These are the previously-missing **safe directions** at b ≥ 3.
-/

namespace E213.Math.Real213.CutSumGeneral

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor

private theorem bool_eq_iff_v2 (a b : Bool)
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- ★★★★★ Same-denominator forward (always holds, any b ≥ 1).

  cutSum (constCut a b) (constCut c b) m k = true
    ⇒ constCut (a + c) b m k = true.

  Proof: from witness i with a·(2k) ≤ b·i AND c·(2k) ≤ b·(2m - i),
  sum: 2ak + 2ck ≤ b·(2m), so 2(a+c)k ≤ 2bm, hence (a+c)k ≤ bm. -/
theorem cutSum_same_denom_forward (a b c m k : Nat)
    (h : cutSum (constCut a b) (constCut c b) m k = true) :
    constCut (a + c) b m k = true := by
  change cutSumAux (constCut a b) (constCut c b) k (2*m) (2*m) = true at h
  rw [cutSumAux_eq_true_iff] at h
  obtain ⟨i, hi, hci, hcsi⟩ := h
  have h_ai : a * (2 * k) ≤ b * i := of_decide_eq_true hci
  have h_ci : c * (2 * k) ≤ b * (2 * m - i) := of_decide_eq_true hcsi
  show decide ((a + c) * k ≤ b * m) = true
  apply decide_eq_true
  -- Sum: a·(2k) + c·(2k) ≤ b·i + b·(2m - i) = b·(2m).
  have h_add_le : a * (2*k) + c * (2*k) ≤ b * i + b * (2*m - i) :=
    Nat.add_le_add h_ai h_ci
  have h_ri : b * i + b * (2*m - i) = b * (2*m) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [h_ri] at h_add_le
  -- LHS = (a+c)·(2k) = 2·((a+c)·k)
  have h_lhs : a * (2*k) + c * (2*k) = 2 * ((a+c) * k) := by
    rw [show a * (2*k) = 2 * (a*k) from by
          rw [Nat.mul_comm a, Nat.mul_assoc, Nat.mul_comm k a]]
    rw [show c * (2*k) = 2 * (c*k) from by
          rw [Nat.mul_comm c, Nat.mul_assoc, Nat.mul_comm k c]]
    rw [← Nat.mul_add, Nat.add_mul]
  -- RHS = b·(2m) = 2·(b·m)
  have h_rhs : b * (2 * m) = 2 * (b * m) := by
    rw [Nat.mul_comm b, Nat.mul_assoc, Nat.mul_comm m b]
  rw [h_lhs, h_rhs] at h_add_le
  exact Nat.le_of_mul_le_mul_left h_add_le (by decide : 0 < 2)

/-- ★★★★★★ Different-denominator forward (rational addition, any b, d).

  cutSum (constCut a b) (constCut c d) m k = true
    ⇒ constCut (a*d + b*c) (b*d) m k = true.

  This is the cross-multiplication form: a/b + c/d = (ad+bc)/(bd).

  Proof: from witness i with a·(2k) ≤ b·i AND c·(2k) ≤ d·(2m - i),
  multiply 1st by d, 2nd by b: 2adk ≤ bdi, 2bck ≤ bd(2m-i).  Sum:
  2(ad+bc)k ≤ 2bdm, hence (ad+bc)k ≤ bdm. -/
theorem cutSum_diff_denom_forward (a b c d m k : Nat)
    (h : cutSum (constCut a b) (constCut c d) m k = true) :
    constCut (a * d + b * c) (b * d) m k = true := by
  change cutSumAux (constCut a b) (constCut c d) k (2*m) (2*m) = true at h
  rw [cutSumAux_eq_true_iff] at h
  obtain ⟨i, hi, hci, hcsi⟩ := h
  have h_ai : a * (2 * k) ≤ b * i := of_decide_eq_true hci
  have h_ci : c * (2 * k) ≤ d * (2 * m - i) := of_decide_eq_true hcsi
  show decide ((a * d + b * c) * k ≤ b * d * m) = true
  apply decide_eq_true
  -- Multiply h_ai by d (left), h_ci by b (left).
  have h_ai_d : d * (a * (2 * k)) ≤ d * (b * i) :=
    Nat.mul_le_mul_left d h_ai
  have h_ci_b : b * (c * (2 * k)) ≤ b * (d * (2 * m - i)) :=
    Nat.mul_le_mul_left b h_ci
  -- Sum.
  have h_sum : d * (a * (2 * k)) + b * (c * (2 * k))
                ≤ d * (b * i) + b * (d * (2 * m - i)) :=
    Nat.add_le_add h_ai_d h_ci_b
  -- RHS simplification: d·(b·i) + b·(d·(2m-i)) = bd·(2m).
  have h_rhs_eq : d * (b * i) + b * (d * (2 * m - i)) = b * d * (2 * m) := by
    have e1 : d * (b * i) = b * d * i := by
      rw [← Nat.mul_assoc, Nat.mul_comm d b]
    have e2 : b * (d * (2 * m - i)) = b * d * (2 * m - i) := by
      rw [← Nat.mul_assoc]
    rw [e1, e2, ← Nat.mul_add]
    congr 1
    omega
  rw [h_rhs_eq] at h_sum
  -- LHS simplification: d·(a·2k) + b·(c·2k) = 2·(ad+bc)·k.
  have h_lhs_eq : d * (a * (2 * k)) + b * (c * (2 * k))
                   = 2 * ((a * d + b * c) * k) := by
    have e1 : d * (a * (2 * k)) = 2 * (a * d * k) := by
      rw [← Nat.mul_assoc d a (2*k), Nat.mul_comm d a,
          Nat.mul_left_comm (a*d) 2 k]
    have e2 : b * (c * (2 * k)) = 2 * (b * c * k) := by
      rw [← Nat.mul_assoc b c (2*k), Nat.mul_left_comm (b*c) 2 k]
    rw [e1, e2, ← Nat.mul_add, Nat.add_mul]
  -- RHS into 2-form: bd·(2m) = 2·(bd·m).
  have h_rhs2 : b * d * (2 * m) = 2 * (b * d * m) := by
    rw [Nat.mul_comm (b*d), Nat.mul_assoc, Nat.mul_comm m (b*d)]
  rw [h_lhs_eq, h_rhs2] at h_sum
  exact Nat.le_of_mul_le_mul_left h_sum (by decide : 0 < 2)

/-- ★★★ Contrapositive (same denom): constCut(a+c, b) false ⇒ cutSum false. -/
theorem cutSum_same_denom_contrapositive (a b c m k : Nat)
    (h : constCut (a + c) b m k = false) :
    cutSum (constCut a b) (constCut c b) m k = false := by
  cases hcs : cutSum (constCut a b) (constCut c b) m k with
  | true =>
    have := cutSum_same_denom_forward a b c m k hcs
    rw [this] at h; cases h
  | false => rfl

/-- ★★★ Contrapositive (different denom): constCut(ad+bc, bd) false ⇒ cutSum false. -/
theorem cutSum_diff_denom_contrapositive (a b c d m k : Nat)
    (h : constCut (a * d + b * c) (b * d) m k = false) :
    cutSum (constCut a b) (constCut c d) m k = false := by
  cases hcs : cutSum (constCut a b) (constCut c d) m k with
  | true =>
    have := cutSum_diff_denom_forward a b c d m k hcs
    rw [this] at h; cases h
  | false => rfl

/-! ### Concrete witnesses at b = 3 (previously blocked) -/

/-- Forward direction at b=3 holds: 1/3 + 1/3 ⇒ 2/3 (via cutSum). -/
example : cutSum (constCut 1 3) (constCut 1 3) 2 3 = true →
    constCut 2 3 2 3 = true :=
  cutSum_same_denom_forward 1 3 1 2 3

/-- Decide test confirming forward at b=3: 1/3 + 1/3 ≤ 2/3 holds. -/
theorem cutSum_thirds_at_compatible :
    cutSum (constCut 1 3) (constCut 1 3) 2 3 = constCut 2 3 2 3 := by decide

/-- Decide test at b=5: 2/5 + 3/5 = 5/5 at (m=5, k=5) (both b∣2k). -/
theorem cutSum_fifths_compatible :
    cutSum (constCut 2 5) (constCut 3 5) 5 5 = constCut 5 5 5 5 := by decide

/-- Precision artifact at b=5, incompatible (m, k): cutSum underestimates. -/
theorem cutSum_fifths_artifact :
    cutSum (constCut 2 5) (constCut 3 5) 1 1 = false
    ∧ constCut 5 5 1 1 = true := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Math.Real213.CutSumGeneral
