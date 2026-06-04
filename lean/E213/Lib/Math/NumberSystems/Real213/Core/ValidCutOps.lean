import E213.Lib.Math.NumberSystems.Real213.Core.ValidCut
import E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin
import E213.Lib.Math.NumberSystems.Real213.Mul.CutDouble
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
/-!
# ValidCutOps: ValidCut closed under cut ops

cutMax/cutMin/cutHalf/cutDouble/cutSum preserve ValidCut.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Core.ValidCutOps

open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection (cutHalf cutMid)
open E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin (cutMax cutMin)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSumAux)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm (cutSumAux_eq_true_iff)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutDouble (cutDouble)

/-- Helper: `(a && b) = true → a = true`.  PURE. -/
private theorem and_left {a b : Bool} (h : (a && b) = true) : a = true :=
  match a, h with
  | true, _ => rfl
  | false, h => Bool.noConfusion h

/-- Helper: `(a && b) = true → b = true`.  PURE. -/
private theorem and_right {a b : Bool} (h : (a && b) = true) : b = true :=
  match a, h with
  | true, h => h
  | false, h => Bool.noConfusion h

private theorem and_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by rw [ha, hb]; rfl

/-- Helper: `(a || b) = true → a = true ∨ b = true`. -/
private theorem or_cases {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true :=
  match a, h with
  | true, _ => Or.inl rfl
  | false, h => Or.inr h

private theorem or_left {a b : Bool} (h : a = true) : (a || b) = true := by
  rw [h]; rfl

private theorem or_right {a b : Bool} (h : b = true) : (a || b) = true := by
  rw [h]; cases a <;> rfl

/-- cutMax preserves ValidCut. -/
theorem cutMax_valid (cx cy : Nat → Nat → Bool)
    (hx : ValidCut cx) (hy : ValidCut cy) : ValidCut (cutMax cx cy) where
  upM := by
    intro m1 m2 k hm h
    show (cx m2 k && cy m2 k) = true
    have h' : (cx m1 k && cy m1 k) = true := h
    exact and_intro (hx.upM m1 m2 k hm (and_left h'))
                    (hy.upM m1 m2 k hm (and_right h'))
  dnK := by
    intro m k1 k2 hk h
    show (cx m k1 && cy m k1) = true
    have h' : (cx m k2 && cy m k2) = true := h
    exact and_intro (hx.dnK m k1 k2 hk (and_left h'))
                    (hy.dnK m k1 k2 hk (and_right h'))

/-- cutMin preserves ValidCut. -/
theorem cutMin_valid (cx cy : Nat → Nat → Bool)
    (hx : ValidCut cx) (hy : ValidCut cy) : ValidCut (cutMin cx cy) where
  upM := by
    intro m1 m2 k hm h
    show (cx m2 k || cy m2 k) = true
    have h' : (cx m1 k || cy m1 k) = true := h
    rcases or_cases h' with h1 | h2
    · exact or_left (hx.upM m1 m2 k hm h1)
    · exact or_right (hy.upM m1 m2 k hm h2)
  dnK := by
    intro m k1 k2 hk h
    show (cx m k1 || cy m k1) = true
    have h' : (cx m k2 || cy m k2) = true := h
    rcases or_cases h' with h1 | h2
    · exact or_left (hx.dnK m k1 k2 hk h1)
    · exact or_right (hy.dnK m k1 k2 hk h2)

/-- cutHalf preserves ValidCut. -/
theorem cutHalf_valid (c : Nat → Nat → Bool) (hc : ValidCut c) :
    ValidCut (cutHalf c) where
  upM := by
    intro m1 m2 k hm h
    show c (2*m2) k = true
    exact hc.upM (2*m1) (2*m2) k (Nat.mul_le_mul_left 2 hm) h
  dnK := by
    intro m k1 k2 hk h
    show c (2*m) k1 = true
    exact hc.dnK (2*m) k1 k2 hk h

/-- cutDouble preserves ValidCut. -/
theorem cutDouble_valid (c : Nat → Nat → Bool) (hc : ValidCut c) :
    ValidCut (cutDouble c) where
  upM := by
    intro m1 m2 k hm h
    show c m2 (2*k) = true
    exact hc.upM m1 m2 (2*k) hm h
  dnK := by
    intro m k1 k2 hk h
    show c m (2*k1) = true
    exact hc.dnK m (2*k1) (2*k2) (Nat.mul_le_mul_left 2 hk) h

/-- cutSum preserves ValidCut. -/
theorem cutSum_valid (cx cy : Nat → Nat → Bool)
    (hx : ValidCut cx) (hy : ValidCut cy) : ValidCut (cutSum cx cy) where
  upM := by
    intro m1 m2 k hm h
    show cutSumAux cx cy k (2*m2) (2*m2) = true
    have h1 : cutSumAux cx cy k (2*m1) (2*m1) = true := h
    obtain ⟨i, hi, hci, hcsi⟩ :=
      (cutSumAux_eq_true_iff _ _ _ _ _).mp h1
    have hi2 : i ≤ 2*m2 := Nat.le_trans hi (Nat.mul_le_mul_left 2 hm)
    have h_le : 2*m1 - i ≤ 2*m2 - i :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hm) i
    exact (cutSumAux_eq_true_iff _ _ _ _ _).mpr
      ⟨i, hi2, hci, hy.upM (2*m1 - i) (2*m2 - i) (2*k) h_le hcsi⟩
  dnK := by
    intro m k1 k2 hk h
    show cutSumAux cx cy k1 (2*m) (2*m) = true
    have h1 : cutSumAux cx cy k2 (2*m) (2*m) = true := h
    obtain ⟨i, hi, hci, hcsi⟩ :=
      (cutSumAux_eq_true_iff _ _ _ _ _).mp h1
    exact (cutSumAux_eq_true_iff _ _ _ _ _).mpr
      ⟨i, hi,
       hx.dnK i (2*k1) (2*k2) (Nat.mul_le_mul_left 2 hk) hci,
       hy.dnK (2*m - i) (2*k1) (2*k2) (Nat.mul_le_mul_left 2 hk) hcsi⟩

/-- cutMid preserves ValidCut (cutMid = cutHalf ∘ cutSum). -/
theorem cutMid_valid (cx cy : Nat → Nat → Bool)
    (hx : ValidCut cx) (hy : ValidCut cy) : ValidCut (cutMid cx cy) :=
  cutHalf_valid (cutSum cx cy) (cutSum_valid cx cy hx hy)

end E213.Lib.Math.NumberSystems.Real213.Core.ValidCutOps
