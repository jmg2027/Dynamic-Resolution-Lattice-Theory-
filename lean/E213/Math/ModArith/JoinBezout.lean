import E213.Hypervisor.Lens.Leaves.ModNat

/-!
# Research.ModJoinBezout: parametric Bezout chain step

Extracts the common pattern of `ModJoinExample` (m=4, k=6) and
`ModJoinCoprime` (m=2, k=3) into a general lemma.

**Core lemma**: `chain_step`.  When L_m and L_k both refine N,
the net +(m-k) step via +m then -k (passing through an intermediate
Raw) is absorbed by N.

## Application

This lemma + induction suffices to construct an arbitrary Bezout-like
chain.
-/

namespace E213.Math.ModArith.JoinBezout

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.LeavesModNat

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
  obtain ⟨w, hw⟩ := E213.Math.Infinity.leaves_surjective_pos
    (Lens.leaves.view r + m) (by omega)
  have h_r_w : (leavesModNat m).view r = (leavesModNat m).view w := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, Nat.add_mod_right]
  have h_w_r' : (leavesModNat k).view w = (leavesModNat k).view r' := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    have : Lens.leaves.view r + m
             = (Lens.leaves.view r + (m - k)) + k := by omega
    rw [this, Nat.add_mod_right]
  exact (hLm _ _ h_r_w).trans (hLk _ _ h_w_r')

end E213.Math.ModArith.JoinBezout

namespace E213.Math.ModArith.JoinBezout

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.LeavesModNat

/-- Same leaves → same N-view via arbitrary L_k. -/
private theorem same_leaves_N {α : Type} (N : Lens α) (k : Nat) (hk : k ≥ 2)
    (hLk : (leavesModNat k).refines N) (r r' : Raw)
    (hr : Lens.leaves.view r = Lens.leaves.view r') :
    N.view r = N.view r' := by
  apply hLk
  show (leavesModNat k).view r = (leavesModNat k).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

/-- +n step via iterated +1 (chain_step_sub with m-k=1). -/
theorem consecutive_step_plus_n {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m = k + 1)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N)
    (r : Raw) (n : Nat) :
    ∀ r', Lens.leaves.view r' = Lens.leaves.view r + n →
        N.view r = N.view r' := by
  induction n with
  | zero =>
      intro r' hr'
      apply same_leaves_N N k hk hLk
      omega
  | succ n ih =>
      intro r' hr'
      have h_r_ge := leaves_ge_one r
      obtain ⟨r'', hr''⟩ :=
        E213.Math.Infinity.leaves_surjective_pos
          (Lens.leaves.view r + n) (by omega)
      have step1 : N.view r = N.view r'' := ih r'' hr''
      have step2 : N.view r'' = N.view r' := by
        apply chain_step_sub N m k hk (by omega) hLm hLk r'' r'
        omega
      exact step1.trans step2

end E213.Math.ModArith.JoinBezout

namespace E213.Math.ModArith.JoinBezout

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.LeavesModNat

/-- **Consecutive coprime → Join = constLens**.
    L_{k+1}.refines N ∧ L_k.refines N → N is constant. -/
theorem consecutive_refines_const {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m = k + 1)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · have heq : Lens.leaves.view r' = Lens.leaves.view r
              + (Lens.leaves.view r' - Lens.leaves.view r) := by omega
    exact consecutive_step_plus_n N m k hk hmk hLm hLk r _ r' heq
  · have heq : Lens.leaves.view r = Lens.leaves.view r'
              + (Lens.leaves.view r - Lens.leaves.view r') := by omega
    exact (consecutive_step_plus_n N m k hk hmk hLm hLk r' _ r heq).symm

end E213.Math.ModArith.JoinBezout
