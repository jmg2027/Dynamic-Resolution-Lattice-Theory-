import E213.Math.Real213.ValidCut
import E213.Math.Real213.CutMaxMin
import E213.Math.Real213.CutDouble
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutSumComm

import E213.Math.Real213.Core
import E213.Math.Real213.CutSum
/-!
# ValidCutOps: ValidCut closed under cut ops

cutMax/cutMin/cutHalf/cutDouble/cutSum preserve ValidCut.
-/

namespace E213.Math.Real213.ValidCutOps

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutHalf cutMid)
open E213.Math.Real213.CutMaxMin (cutMax cutMin)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Math.Real213.CutSumComm (cutSumAux_eq_true_iff)
open E213.Math.Real213.ValidCut (ValidCut)
open E213.Math.Real213.CutDouble (cutDouble)

/-- cutMax preserves ValidCut. -/
theorem cutMax_valid (cx cy : Nat → Nat → Bool)
    (hx : ValidCut cx) (hy : ValidCut cy) : ValidCut (cutMax cx cy) where
  upM := by
    intro m1 m2 k hm h
    show (cx m2 k && cy m2 k) = true
    have h' : (cx m1 k && cy m1 k) = true := h
    rw [Bool.and_eq_true] at h'
    rw [Bool.and_eq_true]
    exact ⟨hx.upM m1 m2 k hm h'.1, hy.upM m1 m2 k hm h'.2⟩
  dnK := by
    intro m k1 k2 hk h
    show (cx m k1 && cy m k1) = true
    have h' : (cx m k2 && cy m k2) = true := h
    rw [Bool.and_eq_true] at h'
    rw [Bool.and_eq_true]
    exact ⟨hx.dnK m k1 k2 hk h'.1, hy.dnK m k1 k2 hk h'.2⟩

/-- cutMin preserves ValidCut. -/
theorem cutMin_valid (cx cy : Nat → Nat → Bool)
    (hx : ValidCut cx) (hy : ValidCut cy) : ValidCut (cutMin cx cy) where
  upM := by
    intro m1 m2 k hm h
    show (cx m2 k || cy m2 k) = true
    have h' : (cx m1 k || cy m1 k) = true := h
    rw [Bool.or_eq_true] at h'
    rw [Bool.or_eq_true]
    rcases h' with h1 | h2
    · exact Or.inl (hx.upM m1 m2 k hm h1)
    · exact Or.inr (hy.upM m1 m2 k hm h2)
  dnK := by
    intro m k1 k2 hk h
    show (cx m k1 || cy m k1) = true
    have h' : (cx m k2 || cy m k2) = true := h
    rw [Bool.or_eq_true] at h'
    rw [Bool.or_eq_true]
    rcases h' with h1 | h2
    · exact Or.inl (hx.dnK m k1 k2 hk h1)
    · exact Or.inr (hy.dnK m k1 k2 hk h2)

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
    rw [cutSumAux_eq_true_iff]
    have h1 : cutSumAux cx cy k (2*m1) (2*m1) = true := h
    rw [cutSumAux_eq_true_iff] at h1
    obtain ⟨i, hi, hci, hcsi⟩ := h1
    have hi2 : i ≤ 2*m2 := Nat.le_trans hi (Nat.mul_le_mul_left 2 hm)
    have h_le : 2*m1 - i ≤ 2*m2 - i := by omega
    exact ⟨i, hi2, hci, hy.upM (2*m1 - i) (2*m2 - i) (2*k) h_le hcsi⟩
  dnK := by
    intro m k1 k2 hk h
    show cutSumAux cx cy k1 (2*m) (2*m) = true
    rw [cutSumAux_eq_true_iff]
    have h1 : cutSumAux cx cy k2 (2*m) (2*m) = true := h
    rw [cutSumAux_eq_true_iff] at h1
    obtain ⟨i, hi, hci, hcsi⟩ := h1
    exact ⟨i, hi,
           hx.dnK i (2*k1) (2*k2) (Nat.mul_le_mul_left 2 hk) hci,
           hy.dnK (2*m - i) (2*k1) (2*k2) (Nat.mul_le_mul_left 2 hk) hcsi⟩

/-- cutMid preserves ValidCut (cutMid = cutHalf ∘ cutSum). -/
theorem cutMid_valid (cx cy : Nat → Nat → Bool)
    (hx : ValidCut cx) (hy : ValidCut cy) : ValidCut (cutMid cx cy) :=
  cutHalf_valid (cutSum cx cy) (cutSum_valid cx cy hx hy)

end E213.Math.Real213.ValidCutOps
