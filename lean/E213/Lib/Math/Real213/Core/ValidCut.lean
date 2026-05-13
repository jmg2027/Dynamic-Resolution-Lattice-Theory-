import E213.Meta.Tactic.Nat213
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest

/-!
# ValidCut: ValidCut — monotone cut function structure

A "valid cut" represents a real number x via the predicate
  c m k = decide(x ≤ m/k)
i.e., true iff x ≤ m/k.  This means:
- **Upward-monotone in m**: m1 ≤ m2 → c m1 k = true → c m2 k = true.
  (Larger m makes "x ≤ m/k" easier to satisfy.)
- **Downward-monotone in k** (in truth): k1 ≤ k2 → c m k2 = true → c m k1 = true.
  (Higher precision k₂ implying truth means lower precision k₁ also.)
-/

namespace E213.Lib.Math.Real213.Core.Core.ValidCut

open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

open E213.Theory E213.Lens

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

/-- **RatioCut**: cuts respect rational ordering.  m1/k1 ≤ m2/k2
    (cross-multiplied: m1*k2 ≤ m2*k1) with k1 ≥ 1 and c m1 k1 →
    c m2 k2.  This is the natural property for cuts representing
    real numbers via cross-multiplied rational comparison. -/
structure RatioCut (c : Nat → Nat → Bool) : Prop where
  ratioMono : ∀ m1 k1 m2 k2, k1 ≥ 1 → m1 * k2 ≤ m2 * k1 →
              c m1 k1 = true → c m2 k2 = true

/-- constCut is RatioCut. -/
theorem constCut_ratio (a b : Nat) : RatioCut (constCut a b) where
  ratioMono := by
    intro m1 k1 m2 k2 hk1 hratio h
    have hak_bm1 : a * k1 ≤ b * m1 := of_decide_eq_true h
    show decide (a*k2 ≤ b*m2) = true
    apply decide_eq_true
    have step1 : a*k1*k2 ≤ b*m1*k2 := Nat.mul_le_mul_right k2 hak_bm1
    have step2 : b*m1*k2 ≤ b*m2*k1 := by
      rw [E213.Tactic.Nat213.mul_assoc, E213.Tactic.Nat213.mul_assoc]
      exact Nat.mul_le_mul_left b hratio
    have step3 : a*k1*k2 ≤ b*m2*k1 := Nat.le_trans step1 step2
    have hrearr_l : a*k1*k2 = k1 * (a*k2) := by
      rw [Nat.mul_comm a k1, E213.Tactic.Nat213.mul_assoc]
    have hrearr_r : b*m2*k1 = k1 * (b*m2) := by
      rw [Nat.mul_comm (b*m2) k1]
    rw [hrearr_l, hrearr_r] at step3
    exact Nat.le_of_mul_le_mul_left step3 hk1

end E213.Lib.Math.Real213.Core.Core.ValidCut
