import E213.Lib.Math.ModArith.JoinBezout
import E213.Lib.Math.NatHelpers.Gcd213

/-!
# ModJoinEuclidean: Euclidean step — L_m + L_k → L_{m-k}

General step via iteration of `ModJoinBezout.chain_step_sub`.

**Theorem**: if m > k ≥ 2 and m - k ≥ 2 then
    `L_m.refines N ∧ L_k.refines N → L_{m-k}.refines N`.

That is, the Euclidean step operates at the Lens refinement level.
-/

namespace E213.Lib.Math.ModArith.JoinEuclidean

open E213.Theory E213.Lens
open E213.Lens.Leaves.ModNat E213.Lib.Math.ModArith.JoinBezout

private theorem leaves_ge_one_local (r : Raw) : 1 ≤ Lens.leaves.view r := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx _ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]
      exact Nat.le_trans ihx (Nat.le_add_right _ _)

private theorem same_leaves_N_local {α : Type} (N : Lens α) (k : Nat)
    (hLk : (leavesModNat k).refines N) (r r' : Raw)
    (hr : Lens.leaves.view r = Lens.leaves.view r') :
    N.view r = N.view r' := by
  apply hLk
  show (leavesModNat k).view r = (leavesModNat k).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

/-- +n*(m-k) step (iteration of chain_step_sub).  ∅-axiom. -/
theorem step_plus_nd {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m > k)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N)
    (r : Raw) (n : Nat) :
    ∀ r', Lens.leaves.view r' = Lens.leaves.view r + n * (m - k) →
        N.view r = N.view r' := by
  induction n with
  | zero =>
      intro r' hr'
      apply same_leaves_N_local N k hLk
      rw [Nat.zero_mul, Nat.add_zero] at hr'
      exact hr'.symm
  | succ n ih =>
      intro r' hr'
      have h_bound : 1 ≤ Lens.leaves.view r + n * (m - k) :=
        Nat.le_trans (leaves_ge_one_local r) (Nat.le_add_right _ _)
      obtain ⟨r'', hr''⟩ :=
        E213.Infinity.leaves_surjective_pos
          (Lens.leaves.view r + n * (m - k)) h_bound
      have step1 : N.view r = N.view r'' := ih r'' hr''
      have hexpand : (n + 1) * (m - k) = n * (m - k) + (m - k) :=
        Nat.succ_mul n (m - k)
      have step2 : N.view r'' = N.view r' := by
        apply chain_step_sub N m k hk hmk hLm hLk r'' r'
        -- view r' = view r + (n+1)*(m-k) = view r + (n*(m-k) + (m-k))
        --        = (view r + n*(m-k)) + (m-k) = view r'' + (m-k)
        rw [hr', hexpand, ← Nat.add_assoc, ← hr'']
      exact step1.trans step2

end E213.Lib.Math.ModArith.JoinEuclidean

namespace E213.Lib.Math.ModArith.JoinEuclidean

open E213.Theory E213.Lens
open E213.Lens.Leaves.ModNat E213.Lib.Math.ModArith.JoinBezout

/-- **Euclidean step**: when m > k ≥ 2 and m - k ≥ 2,
    L_m + L_k → L_{m-k}.  ∅-axiom (uses
    `Gcd213.mod_eq_exists_mul_add` to extract the quotient `q`
    from `view r % (m-k) = view r' % (m-k)`, then iterates
    `step_plus_nd q` times). -/
theorem euclidean_step {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m > k) (hdiff : m - k ≥ 2)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N) :
    (leavesModNat (m - k)).refines N := by
  intro r r' h_equiv
  have h_mod : Lens.leaves.view r % (m - k)
                 = Lens.leaves.view r' % (m - k) := by
    have : (leavesModNat (m - k)).view r
             = (leavesModNat (m - k)).view r' := h_equiv
    rw [leavesModNat_view_eq, leavesModNat_view_eq] at this
    exact this
  have hd_pos : 0 < m - k :=
    Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hdiff
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · obtain ⟨q, hq⟩ := E213.Lib.Math.NatHelpers.Gcd213.mod_eq_exists_mul_add
      (Lens.leaves.view r') (Lens.leaves.view r) (m - k) hd_pos hle h_mod.symm
    exact step_plus_nd N m k hk hmk hLm hLk r q r' hq
  · obtain ⟨q, hq⟩ := E213.Lib.Math.NatHelpers.Gcd213.mod_eq_exists_mul_add
      (Lens.leaves.view r) (Lens.leaves.view r') (m - k) hd_pos hle h_mod
    exact (step_plus_nd N m k hk hmk hLm hLk r' q r hq).symm

end E213.Lib.Math.ModArith.JoinEuclidean
