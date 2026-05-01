import E213.Hypervisor.Lens.Research.Leaves.ModNat

/-!
# Research.ModJoinCoprime: coprime m, k — Join = L_1 = constant

**Theorem (specific case L_2, L_3)**:
`(leavesModNat 2).refines N ∧ (leavesModNat 3).refines N`
→ N.view is constant.

That is, Join(L_2, L_3) = L_1 = constLens (at the refines class level).

## Technique

Bezout: gcd(2, 3) = 1 = 3 - 2.
Chain +1 step: r → (leaves r + 3 via L_3) → (leaves r + 1 via L_2).

Induction on |leaves r' - leaves r| for an arbitrary leaves difference.
-/

namespace E213.Math.ModArith.JoinCoprime

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.LeavesModNat

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

/-- +1 step via L_3 then L_2: chain length 2. -/
private theorem step_plus_one {α : Type} (N : Lens α)
    (h2 : (leavesModNat 2).refines N)
    (h3 : (leavesModNat 3).refines N)
    (r r' : Raw) (hdiff : Lens.leaves.view r' = Lens.leaves.view r + 1) :
    N.view r = N.view r' := by
  obtain ⟨w, hw⟩ := E213.Math.Infinity.leaves_surjective_pos
    (Lens.leaves.view r + 3) (by omega)
  have h_r_w : (leavesModNat 3).view r = (leavesModNat 3).view w := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw]
    omega
  have h_w_r' : (leavesModNat 2).view w = (leavesModNat 2).view r' := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    omega
  exact (h3 _ _ h_r_w).trans (h2 _ _ h_w_r')

/-- Same leaves → same N-view via L_2. -/
private theorem same_leaves {α : Type} (N : Lens α)
    (h2 : (leavesModNat 2).refines N) (r r' : Raw)
    (hr : Lens.leaves.view r = Lens.leaves.view r') :
    N.view r = N.view r' := by
  apply h2
  show (leavesModNat 2).view r = (leavesModNat 2).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

end E213.Math.ModArith.JoinCoprime

namespace E213.Math.ModArith.JoinCoprime

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.LeavesModNat

/-- +k step via iteration. -/
theorem step_plus_k {α : Type} (N : Lens α)
    (h2 : (leavesModNat 2).refines N)
    (h3 : (leavesModNat 3).refines N)
    (r : Raw) (k : Nat) :
    ∀ r', Lens.leaves.view r' = Lens.leaves.view r + k →
        N.view r = N.view r' := by
  induction k with
  | zero =>
      intro r' hr'
      apply same_leaves N h2
      omega
  | succ k ih =>
      intro r' hr'
      have h_r_ge := leaves_ge_one r
      obtain ⟨r'', hr''⟩ :=
        E213.Math.Infinity.leaves_surjective_pos
          (Lens.leaves.view r + k) (by omega)
      have step1 : N.view r = N.view r'' := ih r'' hr''
      have step2 : N.view r'' = N.view r' := by
        apply step_plus_one N h2 h3 r'' r'
        omega
      exact step1.trans step2

end E213.Math.ModArith.JoinCoprime

namespace E213.Math.ModArith.JoinCoprime

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.LeavesModNat

/-- **Main**: L_2.refines N ∧ L_3.refines N → N is constant.
    Concrete proof of Join(L_2, L_3) = L_1 = constLens (gcd = 1). -/
theorem mod_2_3_refines_const {α : Type} (N : Lens α)
    (h2 : (leavesModNat 2).refines N)
    (h3 : (leavesModNat 3).refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · have heq : Lens.leaves.view r' = Lens.leaves.view r
              + (Lens.leaves.view r' - Lens.leaves.view r) := by omega
    exact step_plus_k N h2 h3 r _ r' heq
  · have heq : Lens.leaves.view r = Lens.leaves.view r'
              + (Lens.leaves.view r - Lens.leaves.view r') := by omega
    exact (step_plus_k N h2 h3 r' _ r heq).symm

end E213.Math.ModArith.JoinCoprime
