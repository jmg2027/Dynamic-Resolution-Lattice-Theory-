import E213.Lens.Congruence
import E213.Lens.Instances

/-!
# ModJoinExample: concrete example of Join = gcd

Concrete instance of the "Join = gcd" claim in Note 45 §3.

**Claim**: L_4.refines N ∧ L_6.refines N → L_2.refines N (partial).

Proved via the chain technique: for given r, r', construct an
intermediate r_w and connect the steps using L_4 / L_6.

## Simple example

r = Raw.a (leaves 1), r' is a Raw with leaves 3.  Chain:
- Raw.a (leaves 1) ~_L_6 r_7 (leaves 7): 1 ≡ 7 mod 6.
- r_7 (leaves 7) ~_L_4 r' (leaves 3): 7 ≡ 3 mod 4.

Combined: N.view Raw.a = N.view r'.
-/

namespace E213.Lib.Math.ModArith.JoinExample

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat

/-- Chain example: L_4 + L_6 → N equates leaves-1 and leaves-3. -/
theorem mod_4_6_chain_example {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N)
    (h6 : (leavesModNat 6).refines N) :
    ∀ r : Raw, Lens.leaves.view r = 3 → N.view Raw.a = N.view r := by
  intro r hr
  obtain ⟨r_7, hr_7⟩ := E213.Lens.Cardinality.leaves_surjective_pos 7 (by decide)
  have h_leaves_a : Lens.leaves.view Raw.a = 1 := rfl
  -- Step 1: Raw.a ~_L_6 r_7  (1 ≡ 7 mod 6)
  have h_1_7 : (leavesModNat 6).view Raw.a = (leavesModNat 6).view r_7 := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, h_leaves_a, hr_7]
  -- Step 2: r_7 ~_L_4 r  (7 ≡ 3 mod 4)
  have h_7_3 : (leavesModNat 4).view r_7 = (leavesModNat 4).view r := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hr_7, hr]
  -- Chain via N.
  have step1 : N.view Raw.a = N.view r_7 := h6 _ _ h_1_7
  have step2 : N.view r_7 = N.view r := h4 _ _ h_7_3
  exact step1.trans step2


/-- +2 step via L_6 then L_4: chain of length 2. -/
theorem mod_4_6_step_two {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N)
    (h6 : (leavesModNat 6).refines N)
    (r r' : Raw) (hdiff : Lens.leaves.view r' = Lens.leaves.view r + 2) :
    N.view r = N.view r' := by
  have hadd6_pos : 0 < Lens.leaves.view r + 6 :=
    Nat.lt_of_lt_of_le (by decide : (0:Nat) < 6) (Nat.le_add_left _ _)
  obtain ⟨w, hw⟩ := E213.Lens.Cardinality.leaves_surjective_pos
    (Lens.leaves.view r + 6) hadd6_pos
  have h_r_w : (leavesModNat 6).view r = (leavesModNat 6).view w := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw]
    -- Goal: view r % 6 = (view r + 6) % 6
    exact (E213.Tactic.NatHelper.add_self_mod_pure (Lens.leaves.view r) 6).symm
  have h_w_r' : (leavesModNat 4).view w = (leavesModNat 4).view r' := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    -- Goal: (view r + 6) % 4 = (view r + 2) % 4
    have h_split : Lens.leaves.view r + 6 = (Lens.leaves.view r + 2) + 4 := by
      rw [Nat.add_assoc]
    rw [h_split]
    exact E213.Tactic.NatHelper.add_self_mod_pure (Lens.leaves.view r + 2) 4
  exact (h6 _ _ h_r_w).trans (h4 _ _ h_w_r')

/-- Same leaves → same N-view (via L_4). -/
private theorem same_leaves_same_N {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N) (r r' : Raw)
    (hr : Lens.leaves.view r = Lens.leaves.view r') :
    N.view r = N.view r' := by
  apply h4
  show (leavesModNat 4).view r = (leavesModNat 4).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

open E213.Lens renaming leaves_view_pos → leaves_ge_one

/-- General chain: +2k step. -/
theorem mod_4_6_step_2k {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N)
    (h6 : (leavesModNat 6).refines N) (r : Raw) (k : Nat) :
    ∀ r', Lens.leaves.view r' = Lens.leaves.view r + 2 * k →
        N.view r = N.view r' := by
  induction k with
  | zero =>
      intro r' hr'
      apply same_leaves_same_N N h4
      -- hr' : Lens.leaves.view r' = Lens.leaves.view r + 2 * 0
      -- 2 * 0 = 0, view r + 0 = view r, so view r' = view r.
      have h_eq : Lens.leaves.view r + 2 * 0 = Lens.leaves.view r := by
        rw [Nat.mul_zero, Nat.add_zero]
      exact (hr'.trans h_eq).symm
  | succ k ih =>
      intro r' hr'
      have h_r_ge := leaves_ge_one r
      have h_r_add_2k_pos : 0 < Lens.leaves.view r + 2 * k :=
        Nat.lt_of_lt_of_le h_r_ge (Nat.le_add_right _ _)
      obtain ⟨r'', hr''⟩ :=
        E213.Lens.Cardinality.leaves_surjective_pos
          (Lens.leaves.view r + 2 * k) h_r_add_2k_pos
      have step1 : N.view r = N.view r'' := ih r'' hr''
      have step2 : N.view r'' = N.view r' := by
        apply mod_4_6_step_two N h4 h6 r'' r'
        -- hr' : view r' = view r + 2 * (k + 1)
        -- hr'' : view r'' = view r + 2 * k
        -- Goal: view r' = view r'' + 2
        have h_step : Lens.leaves.view r + 2 * (k + 1)
                    = (Lens.leaves.view r + 2 * k) + 2 := by
          rw [Nat.mul_succ, ← Nat.add_assoc]
        rw [hr', h_step, ← hr'']
      exact step1.trans step2


/-- **L_4 + L_6 → L_2 complete**.  Least direction of
    Join(L_4, L_6) = L_2 = L_gcd(4,6) in the refines preorder. -/
theorem mod_4_6_refines_parity {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N)
    (h6 : (leavesModNat 6).refines N) :
    (leavesModNat 2).refines N := by
  intro r r' h_parity
  have hp : Lens.leaves.view r % 2 = Lens.leaves.view r' % 2 := by
    have : (leavesModNat 2).view r = (leavesModNat 2).view r' := h_parity
    rw [leavesModNat_view_eq, leavesModNat_view_eq] at this
    exact this
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · obtain ⟨k, hk⟩ : ∃ k, Lens.leaves.view r' = Lens.leaves.view r + 2 * k := by
      refine ⟨(Lens.leaves.view r' - Lens.leaves.view r) / 2, ?_⟩
      -- view r' = view r + 2 * ((view r' - view r) / 2).
      -- Use mod_diff_eq_zero_of_le + div_add_mod.
      have hmod0 : (Lens.leaves.view r' - Lens.leaves.view r) % 2 = 0 :=
        E213.Meta.Nat.AddMod213.mod_diff_eq_zero_of_le
          (by decide : (0:Nat) < 2) hle hp
      have hdam :
          2 * ((Lens.leaves.view r' - Lens.leaves.view r) / 2)
          + (Lens.leaves.view r' - Lens.leaves.view r) % 2
          = Lens.leaves.view r' - Lens.leaves.view r :=
        E213.Meta.Nat.AddMod213.div_add_mod _ 2
      have h2div :
          2 * ((Lens.leaves.view r' - Lens.leaves.view r) / 2)
          = Lens.leaves.view r' - Lens.leaves.view r := by
        rw [hmod0, Nat.add_zero] at hdam; exact hdam
      have hsac : Lens.leaves.view r' - Lens.leaves.view r + Lens.leaves.view r
                = Lens.leaves.view r' :=
        E213.Tactic.NatHelper.sub_add_cancel hle
      -- view r + (view r' - view r) = view r' - view r + view r = view r'.
      have hcomm :
          Lens.leaves.view r + (Lens.leaves.view r' - Lens.leaves.view r)
          = Lens.leaves.view r' - Lens.leaves.view r + Lens.leaves.view r :=
        Nat.add_comm _ _
      have hsum :
          Lens.leaves.view r + (Lens.leaves.view r' - Lens.leaves.view r)
          = Lens.leaves.view r' := hcomm.trans hsac
      rw [h2div]; exact hsum.symm
    exact mod_4_6_step_2k N h4 h6 r k r' hk
  · obtain ⟨k, hk⟩ : ∃ k, Lens.leaves.view r = Lens.leaves.view r' + 2 * k := by
      refine ⟨(Lens.leaves.view r - Lens.leaves.view r') / 2, ?_⟩
      have hmod0 : (Lens.leaves.view r - Lens.leaves.view r') % 2 = 0 :=
        E213.Meta.Nat.AddMod213.mod_diff_eq_zero_of_le
          (by decide : (0:Nat) < 2) hle hp.symm
      have hdam :
          2 * ((Lens.leaves.view r - Lens.leaves.view r') / 2)
          + (Lens.leaves.view r - Lens.leaves.view r') % 2
          = Lens.leaves.view r - Lens.leaves.view r' :=
        E213.Meta.Nat.AddMod213.div_add_mod _ 2
      have h2div :
          2 * ((Lens.leaves.view r - Lens.leaves.view r') / 2)
          = Lens.leaves.view r - Lens.leaves.view r' := by
        rw [hmod0, Nat.add_zero] at hdam; exact hdam
      have hsac : Lens.leaves.view r - Lens.leaves.view r' + Lens.leaves.view r'
                = Lens.leaves.view r :=
        E213.Tactic.NatHelper.sub_add_cancel hle
      have hcomm :
          Lens.leaves.view r' + (Lens.leaves.view r - Lens.leaves.view r')
          = Lens.leaves.view r - Lens.leaves.view r' + Lens.leaves.view r' :=
        Nat.add_comm _ _
      have hsum :
          Lens.leaves.view r' + (Lens.leaves.view r - Lens.leaves.view r')
          = Lens.leaves.view r := hcomm.trans hsac
      rw [h2div]; exact hsum.symm
    exact (mod_4_6_step_2k N h4 h6 r' k r hk).symm

end E213.Lib.Math.ModArith.JoinExample
