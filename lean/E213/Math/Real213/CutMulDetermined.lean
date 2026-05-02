import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumDetermined

/-!
# Research.Real213CutMulDetermined: cutMul locality

locally-determined property of cutMul — bounded 2D search.
-/

namespace E213.Math.Real213.CutMulDetermined

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSumDetermined (isLocallyDetermined2)
open E213.Math.Real213.CutMul (cutMul cutMulInner cutMulOuter)
open E213.Math.Real213.Core (Real213)

/-- congruence of cutMulInner — m1 fixed, iterate m2. -/
theorem cutMulInner_congr (k m m1 m2Bound : Nat)
    (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : cx1 m1 k = cx2 m1 k)
    (hy : ∀ m', m' ≤ m2Bound → cy1 m' k = cy2 m' k)
    (n : Nat) (hn : n ≤ m2Bound) :
    cutMulInner cx1 cy1 k m m1 n = cutMulInner cx2 cy2 k m m1 n := by
  induction n with
  | zero =>
    show (cx1 m1 k && cy1 0 k && decide (m1 * 0 ≤ m * k))
       = (cx2 m1 k && cy2 0 k && decide (m1 * 0 ≤ m * k))
    rw [hx, hy 0 (Nat.zero_le _)]
  | succ i ih =>
    have hi : i ≤ m2Bound := Nat.le_of_succ_le hn
    show ((cx1 m1 k && cy1 (i+1) k && decide (m1 * (i+1) ≤ m * k))
            || cutMulInner cx1 cy1 k m m1 i)
       = ((cx2 m1 k && cy2 (i+1) k && decide (m1 * (i+1) ≤ m * k))
            || cutMulInner cx2 cy2 k m m1 i)
    rw [hx, hy (i+1) hn, ih hi]

end E213.Math.Real213.CutMulDetermined

namespace E213.Math.Real213.CutMulDetermined

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSumDetermined (isLocallyDetermined2)
open E213.Math.Real213.CutMul (cutMul cutMulInner cutMulOuter)
open E213.Math.Real213.Core (Real213)

/-- congruence of cutMulOuter — iterate m1. -/
theorem cutMulOuter_congr (k m m1Bound m2Bound : Nat)
    (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : ∀ m', m' ≤ m1Bound → cx1 m' k = cx2 m' k)
    (hy : ∀ m', m' ≤ m2Bound → cy1 m' k = cy2 m' k)
    (n : Nat) (hn : n ≤ m1Bound) :
    cutMulOuter cx1 cy1 k m m2Bound n = cutMulOuter cx2 cy2 k m m2Bound n := by
  induction n with
  | zero =>
    show cutMulInner cx1 cy1 k m 0 m2Bound = cutMulInner cx2 cy2 k m 0 m2Bound
    exact cutMulInner_congr k m 0 m2Bound cx1 cx2 cy1 cy2
            (hx 0 (Nat.zero_le _)) hy m2Bound (Nat.le_refl _)
  | succ i ih =>
    have hi : i ≤ m1Bound := Nat.le_of_succ_le hn
    show (cutMulInner cx1 cy1 k m (i+1) m2Bound
            || cutMulOuter cx1 cy1 k m m2Bound i)
       = (cutMulInner cx2 cy2 k m (i+1) m2Bound
            || cutMulOuter cx2 cy2 k m m2Bound i)
    have step1 : cutMulInner cx1 cy1 k m (i+1) m2Bound
               = cutMulInner cx2 cy2 k m (i+1) m2Bound :=
      cutMulInner_congr k m (i+1) m2Bound cx1 cx2 cy1 cy2
        (hx (i+1) hn) hy m2Bound (Nat.le_refl _)
    rw [step1, ih hi]

end E213.Math.Real213.CutMulDetermined

namespace E213.Math.Real213.CutMulDetermined

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutMul (cutMul cutMulInner cutMulOuter)
open E213.Math.Real213.CutSumDetermined (isLocallyDetermined2)
open E213.Math.Real213.Core (Real213)

/-- **cutMul is locally determined**: N = (m+1)*(k+1). -/
theorem cutMul_locallyDetermined : isLocallyDetermined2 cutMul := by
  intro m k
  refine ⟨(m+1) * (k+1), ?_⟩
  intro cx1 cx2 cy1 cy2 hx hy
  show cutMulOuter cx1 cy1 k m ((m+1)*(k+1)) ((m+1)*(k+1))
     = cutMulOuter cx2 cy2 k m ((m+1)*(k+1)) ((m+1)*(k+1))
  have hk_le : k ≤ (m+1)*(k+1) := by
    have h1 : k ≤ k + 1 := Nat.le_succ k
    have h2 : k + 1 ≤ (m+1)*(k+1) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact Nat.le_trans h1 h2
  apply cutMulOuter_congr
  · intro m' hm'
    exact hx m' k hm' hk_le
  · intro m' hm'
    exact hy m' k hm' hk_le
  · exact Nat.le_refl _

end E213.Math.Real213.CutMulDetermined
