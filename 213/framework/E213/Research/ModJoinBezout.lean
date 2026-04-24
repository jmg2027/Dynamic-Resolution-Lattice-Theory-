import E213.Research.LeavesModNat

/-!
# Research.ModJoinBezout: parametric Bezout chain step

`ModJoinExample` (m=4, k=6) 와 `ModJoinCoprime` (m=2, k=3) 의
공통 패턴을 일반화 lemma 로 추출.

**Core lemma**: `chain_step`.  L_m + L_k 이 N 에 refine 될
때, +m then -k (intermediate Raw 를 거쳐서) 의 net +(m-k) step
이 N 에 의해 absorbed.

## 적용

이 lemma + induction 으로 임의 Bezout-like chain 구성 가능.
-/

namespace E213.Research.ModJoinBezout

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat

private theorem leaves_ge_one (r : Raw) : 1 ≤ Lens.leaves.view r := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]; omega

/-- **Chain step**: L_m + L_k → +(m - k) step (for m > k ≥ 2).
    Intermediate Raw with leaves = leaves r + m. -/
theorem chain_step_sub {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m > k)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N)
    (r r' : Raw) (hdiff : Lens.leaves.view r' = Lens.leaves.view r + (m - k)) :
    N.view r = N.view r' := by
  obtain ⟨w, hw⟩ := E213.Infinity.leaves_surjective_pos
    (Lens.leaves.view r + m) (by omega)
  have h_r_w : (leavesModNat m).view r = (leavesModNat m).view w := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, Nat.add_mod_right]
  have h_w_r' : (leavesModNat k).view w = (leavesModNat k).view r' := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    have : Lens.leaves.view r + m
             = (Lens.leaves.view r + (m - k)) + k := by omega
    rw [this, Nat.add_mod_right]
  exact (hLm _ _ h_r_w).trans (hLk _ _ h_w_r')

end E213.Research.ModJoinBezout
