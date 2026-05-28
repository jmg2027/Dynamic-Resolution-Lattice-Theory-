import E213.Lens.Congruence
import E213.Lens.Instances
import E213.Meta.Nat.NatDiv213

/-!
# ModJoinBezout: parametric Bezout chain step

Extracts the common pattern of `ModJoinExample` (m=4, k=6) and
`ModJoinCoprime` (m=2, k=3) into a general lemma.

**Core lemma**: `chain_step`.  When L_m and L_k both refine N,
the net +(m-k) step via +m then -k (passing through an intermediate
Raw) is absorbed by N.

## Application

This lemma + induction suffices to construct an arbitrary Bezout-like
chain.
-/

namespace E213.Lib.Math.ModArith.JoinBezout

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat

open E213.Lens renaming leaves_view_pos → leaves_ge_one

/-- **Chain step**: L_m + L_k → +(m - k) step (for m > k ≥ 2).
    Intermediate Raw with leaves = leaves r + m.  ∅-axiom. -/
theorem chain_step_sub {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m > k)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N)
    (r r' : Raw) (hdiff : Lens.leaves.view r' = Lens.leaves.view r + (m - k)) :
    N.view r = N.view r' := by
  have h_pos : 1 ≤ Lens.leaves.view r + m :=
    Nat.le_trans (leaves_ge_one r) (Nat.le_add_right _ _)
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hk
  have hm_pos : 0 < m := Nat.lt_trans hk_pos hmk
  obtain ⟨w, hw⟩ := E213.Lens.Cardinality.leaves_surjective_pos
    (Lens.leaves.view r + m) h_pos
  have h_r_w : (leavesModNat m).view r = (leavesModNat m).view w := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw,
        E213.Meta.Nat.NatDiv213.add_mod_right_pos hm_pos]
  have h_w_r' : (leavesModNat k).view w = (leavesModNat k).view r' := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    have hkm_le : k ≤ m := Nat.le_of_lt hmk
    have h_sub_add : (m - k) + k = m :=
      E213.Tactic.NatHelper.sub_add_cancel hkm_le
    have hrewrite : Lens.leaves.view r + m
                      = (Lens.leaves.view r + (m - k)) + k := by
      rw [Nat.add_assoc, h_sub_add]
    rw [hrewrite, E213.Meta.Nat.NatDiv213.add_mod_right_pos hk_pos]
  exact (hLm _ _ h_r_w).trans (hLk _ _ h_w_r')


/-- Same leaves → same N-view via arbitrary L_k. -/
private theorem same_leaves_N {α : Type} (N : Lens α) (k : Nat) (hk : k ≥ 2)
    (hLk : (leavesModNat k).refines N) (r r' : Raw)
    (hr : Lens.leaves.view r = Lens.leaves.view r') :
    N.view r = N.view r' := by
  apply hLk
  show (leavesModNat k).view r = (leavesModNat k).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

/-- +n step via iterated +1 (chain_step_sub with m-k=1).  ∅-axiom. -/
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
      rw [Nat.add_zero] at hr'
      exact hr'.symm
  | succ n ih =>
      intro r' hr'
      have h_pos : 1 ≤ Lens.leaves.view r + n :=
        Nat.le_trans (leaves_ge_one r) (Nat.le_add_right _ _)
      obtain ⟨r'', hr''⟩ :=
        E213.Lens.Cardinality.leaves_surjective_pos (Lens.leaves.view r + n) h_pos
      have step1 : N.view r = N.view r'' := ih r'' hr''
      have hmk_lt : m > k := by rw [hmk]; exact Nat.lt_succ_self k
      have hmk_diff : m - k = 1 := by
        rw [hmk]; exact E213.Meta.Nat.Gcd213.succ_sub_self_213 k
      have step2 : N.view r'' = N.view r' := by
        apply chain_step_sub N m k hk hmk_lt hLm hLk r'' r'
        -- Need: view r' = view r'' + (m - k) = view r'' + 1
        rw [hmk_diff, hr', hr'']
        -- view r + (n + 1) = (view r + n) + 1
        rw [Nat.add_succ]
      exact step1.trans step2


/-- **Consecutive coprime → Join = constLens**.
    L_{k+1}.refines N ∧ L_k.refines N → N is constant.  ∅-axiom. -/
theorem consecutive_refines_const {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m = k + 1)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · have heq : Lens.leaves.view r' = Lens.leaves.view r
              + (Lens.leaves.view r' - Lens.leaves.view r) :=
      (E213.Tactic.NatHelper.add_sub_of_le hle).symm
    exact consecutive_step_plus_n N m k hk hmk hLm hLk r _ r' heq
  · have heq : Lens.leaves.view r = Lens.leaves.view r'
              + (Lens.leaves.view r - Lens.leaves.view r') :=
      (E213.Tactic.NatHelper.add_sub_of_le hle).symm
    exact (consecutive_step_plus_n N m k hk hmk hLm hLk r' _ r heq).symm

end E213.Lib.Math.ModArith.JoinBezout
