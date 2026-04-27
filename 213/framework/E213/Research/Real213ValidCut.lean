import E213.Research.Real213CutSum
import E213.Research.Real213CutSumTest

/-!
# Research.Real213ValidCut: ValidCut — monotone cut function structure

A "valid cut" represents a real number x via the predicate
  c m k = decide(x ≤ m/k)
i.e., true iff x ≤ m/k.  This means:
- **Upward-monotone in m**: m1 ≤ m2 → c m1 k = true → c m2 k = true.
  (Larger m makes "x ≤ m/k" easier to satisfy.)
- **Downward-monotone in k** (in truth): k1 ≤ k2 → c m k2 = true → c m k1 = true.
  (Higher precision k₂ implying truth means lower precision k₁ also.)
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **ValidCut**: cut function with the two monotonicity properties
    of a real-number cut. -/
structure ValidCut (c : Nat → Nat → Bool) : Prop where
  upM : ∀ m1 m2 k, m1 ≤ m2 → c m1 k = true → c m2 k = true
  dnK : ∀ m k1 k2, k1 ≤ k2 → c m k2 = true → c m k1 = true

/-- constCut is a ValidCut. -/
theorem constCut_valid (a b : Nat) : ValidCut (constCut a b) where
  upM := by
    intro m1 m2 k hm h
    have hak_bm1 : a * k ≤ b * m1 := of_decide_eq_true h
    show decide (a*k ≤ b*m2) = true
    apply decide_eq_true
    exact Nat.le_trans hak_bm1 (Nat.mul_le_mul_left b hm)
  dnK := by
    intro m k1 k2 hk h
    have hak2_bm : a * k2 ≤ b * m := of_decide_eq_true h
    show decide (a*k1 ≤ b*m) = true
    apply decide_eq_true
    exact Nat.le_trans (Nat.mul_le_mul_left a hk) hak2_bm

end E213.Research.Real213CutSum
