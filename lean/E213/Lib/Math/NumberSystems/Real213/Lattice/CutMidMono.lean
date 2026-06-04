import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCutOps
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCut
/-!
# CutMidMono: cutMid monotonicity (RatioCut)

For a, b RatioCut and cutLe a b, we prove cutLe a (cutMid a b).

Strategy:
- cutMid a b m k = true ⟹ ∃ i ≤ 4m, a i (2k) ∧ b (4m - i) (2k).
- cutLe a b lifts b ↦ a at the witness.
- min(i, 4m - i) ≤ 2m.  Use RatioCut to scale down to (m, k).
- Requires k ≥ 1 (RatioCut needs k1 ≥ 1).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Lattice.CutMidMono

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Bisection.CutBisection (cutMid)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutLe)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSumAux)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumComm (cutSumAux_eq_true_iff)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (RatioCut)

/-- cutLe a (cutMid a b) at fixed (m, k) with k ≥ 1, for RatioCut a
    and cutLe a b.  Stated as pointwise (Bool equality form). -/
theorem cutLe_a_cutMid_at (a b : Nat → Nat → Bool)
    (hra : RatioCut a) (hle : cutLe a b)
    (m k : Nat) (hk : k ≥ 1)
    (hmid : cutMid a b m k = true) : a m k = true := by
  have h1 : cutSumAux a b k (2*(2*m)) (2*(2*m)) = true := hmid
  obtain ⟨i, hi, hai, hbi⟩ := (cutSumAux_eq_true_iff _ _ _ _ _).mp h1
  have ha2 : a (2*(2*m) - i) (2*k) = true := hle (2*(2*m) - i) (2*k) hbi
  have h_2k : 2*k ≥ 1 :=
    Nat.le_trans hk (Nat.le_mul_of_pos_left k (by decide : 0 < 2))
  match Nat.decLe i (2*m) with
  | isTrue hcase =>
    have hratio : i * k ≤ m * (2*k) := by
      have e : m * (2*k) = 2*m*k := by
        rw [← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm m 2]
      rw [e]
      exact Nat.mul_le_mul_right k hcase
    exact hra.ratioMono i (2*k) m k h_2k hratio hai
  | isFalse hcase =>
    have h_2m_le_i : 2*m ≤ i := by
      rcases Nat.le_total i (2*m) with h | h
      · exact absurd h hcase
      · exact h
    have h_4m_i : 2*(2*m) - i ≤ 2*m := by
      calc 2*(2*m) - i ≤ 2*(2*m) - 2*m :=
              E213.Tactic.NatHelper.sub_le_sub_left (2*(2*m)) h_2m_le_i
        _ = (2*m + 2*m) - 2*m := by rw [E213.Tactic.NatHelper.two_mul]
        _ = 2*m := E213.Tactic.NatHelper.add_sub_cancel_right (2*m) (2*m)
    have hratio : (2*(2*m) - i) * k ≤ m * (2*k) := by
      have e : m * (2*k) = 2*m*k := by
        rw [← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm m 2]
      rw [e]
      exact Nat.mul_le_mul_right k h_4m_i
    exact hra.ratioMono (2*(2*m) - i) (2*k) m k h_2k hratio ha2

/-- cutLe (cutMid a b) b at fixed (m, k) with k ≥ 1.
    Witness i = 2m: bracket midpoint b at (2m, 2k) = b at (m, k). -/
theorem cutLe_cutMid_b_at (a b : Nat → Nat → Bool)
    (hrb : RatioCut b) (hle : cutLe a b)
    (m k : Nat) (hk : k ≥ 1)
    (hb : b m k = true) : cutMid a b m k = true := by
  show cutSumAux a b k (2*(2*m)) (2*(2*m)) = true
  apply (cutSumAux_eq_true_iff _ _ _ _ _).mpr
  -- Witness i = 2*m.
  refine ⟨2*m, ?_, ?_, ?_⟩
  · -- 2m ≤ 4m
    exact Nat.le_mul_of_pos_left (2*m) (by decide : 0 < 2)
  · -- a (2m) (2k) = true.  Use cutLe a b backwards: from b (2m) (2k).
    -- b (2m) (2k) = true via RatioCut b.
    have hb2 : b (2*m) (2*k) = true := by
      apply hrb.ratioMono m k (2*m) (2*k) hk
      · -- m * (2k) ≤ (2m) * k.  Both = 2mk.
        have e1 : m * (2*k) = 2*m*k := by
          rw [← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm m 2]
        have e2 : (2*m) * k = 2*m*k := rfl
        rw [e1, e2]
        exact Nat.le_refl _
      · exact hb
    exact hle (2*m) (2*k) hb2
  · -- b (4m - 2m) (2k) = b (2m) (2k) = true.
    have heq : 2*(2*m) - 2*m = 2*m := by
      rw [E213.Tactic.NatHelper.two_mul]
      exact E213.Tactic.NatHelper.add_sub_cancel_right (2*m) (2*m)
    rw [heq]
    apply hrb.ratioMono m k (2*m) (2*k) hk
    · have e1 : m * (2*k) = 2*m*k := by
        rw [← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm m 2]
      have e2 : (2*m) * k = 2*m*k := rfl
      rw [e1, e2]
      exact Nat.le_refl _
    · exact hb

end E213.Lib.Math.NumberSystems.Real213.Lattice.CutMidMono
