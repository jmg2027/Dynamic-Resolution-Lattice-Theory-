import E213.Research.ModJoinBezout

/-!
# Research.ModJoinEuclidean: Euclidean step — L_m + L_k → L_{m-k}

`ModJoinBezout.chain_step_sub` 의 iteration 으로 일반 step.

**정리**: m > k ≥ 2 이고 m - k ≥ 2 이면
    `L_m.refines N ∧ L_k.refines N → L_{m-k}.refines N`.

즉 Euclidean step 이 Lens refinement level 에서 작동.
-/

namespace E213.Research.ModJoinEuclidean

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat E213.Research.ModJoinBezout

private theorem leaves_ge_one_local (r : Raw) : 1 ≤ Lens.leaves.view r := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]; omega

private theorem same_leaves_N_local {α : Type} (N : Lens α) (k : Nat)
    (hLk : (leavesModNat k).refines N) (r r' : Raw)
    (hr : Lens.leaves.view r = Lens.leaves.view r') :
    N.view r = N.view r' := by
  apply hLk
  show (leavesModNat k).view r = (leavesModNat k).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

/-- +n*(m-k) step (iteration of chain_step_sub). -/
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
      omega
  | succ n ih =>
      intro r' hr'
      have h_r_ge : 1 ≤ Lens.leaves.view r := leaves_ge_one_local r
      have h_bound : 1 ≤ Lens.leaves.view r + n * (m - k) := by
        have : 0 ≤ n * (m - k) := Nat.zero_le _
        omega
      obtain ⟨r'', hr''⟩ :=
        E213.Infinity.leaves_surjective_pos
          (Lens.leaves.view r + n * (m - k)) h_bound
      have step1 : N.view r = N.view r'' := ih r'' hr''
      have hexpand : (n + 1) * (m - k) = n * (m - k) + (m - k) :=
        Nat.succ_mul n (m - k)
      have step2 : N.view r'' = N.view r' := by
        apply chain_step_sub N m k hk hmk hLm hLk r'' r'
        rw [hr', hr'', hexpand]
        omega
      exact step1.trans step2

end E213.Research.ModJoinEuclidean

namespace E213.Research.ModJoinEuclidean

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat E213.Research.ModJoinBezout

/-- **Euclidean step**: m > k ≥ 2, m - k ≥ 2 인 경우
    L_m + L_k → L_{m-k}. -/
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
  have hd_pos : m - k > 0 := by omega
  have key : ∀ (a b : Nat), a % (m - k) = b % (m - k) → b ≤ a →
             a = b + ((a - b) / (m - k)) * (m - k) := by
    intro a b hmod hab
    have h1 := Nat.div_add_mod a (m - k)
    have h2 := Nat.div_add_mod b (m - k)
    have hb_le_a_div : b / (m - k) ≤ a / (m - k) := by
      have hamod := Nat.mod_lt a hd_pos
      have hbmod := Nat.mod_lt b hd_pos
      by_cases hle : b / (m - k) ≤ a / (m - k)
      · exact hle
      · exfalso
        have hlt : a / (m - k) < b / (m - k) := Nat.lt_of_not_le hle
        have hgt : b / (m - k) ≥ a / (m - k) + 1 := hlt
        have hmul_ge : (m - k) * (a / (m - k) + 1) ≤ (m - k) * (b / (m - k)) :=
          Nat.mul_le_mul_left _ hgt
        have hexp : (m - k) * (a / (m - k) + 1)
                      = (m - k) * (a / (m - k)) + (m - k) :=
          Nat.mul_succ (m - k) (a / (m - k))
        omega
    have hsub : a - b = (m - k) * (a / (m - k) - b / (m - k)) := by
      rw [Nat.mul_sub_left_distrib]; omega
    rw [hsub, Nat.mul_div_cancel_left _ hd_pos, Nat.mul_comm]
    omega
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · exact step_plus_nd N m k hk hmk hLm hLk r _ r'
      (key _ _ h_mod.symm hle)
  · exact (step_plus_nd N m k hk hmk hLm hLk r' _ r
      (key _ _ h_mod hle)).symm

end E213.Research.ModJoinEuclidean
