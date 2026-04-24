import E213.Research.LeavesModNat

/-!
# Research.ModJoinExample: Join = gcd 의 concrete 예

Note 45 §3 의 "Join = gcd" 주장의 구체 instance.

**주장**: L_4.refines N ∧ L_6.refines N → L_2.refines N (부분적).

Chain 기법으로 증명: 주어진 r, r' 에 대해 intermediate r_w 를
construct 하여 L_4 / L_6 단계로 연결.

## 간단한 예

r = Raw.a (leaves 1), r' 은 leaves 3 인 Raw.  Chain:
- Raw.a (leaves 1) ~_L_6 r_7 (leaves 7): 1 ≡ 7 mod 6.
- r_7 (leaves 7) ~_L_4 r' (leaves 3): 7 ≡ 3 mod 4.

결합: N.view Raw.a = N.view r'.
-/

namespace E213.Research.ModJoinExample

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat

/-- Chain example: L_4 + L_6 → N equates leaves-1 and leaves-3. -/
theorem mod_4_6_chain_example {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N)
    (h6 : (leavesModNat 6).refines N) :
    ∀ r : Raw, Lens.leaves.view r = 3 → N.view Raw.a = N.view r := by
  intro r hr
  obtain ⟨r_7, hr_7⟩ := E213.Infinity.leaves_surjective_pos 7 (by omega)
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

end E213.Research.ModJoinExample

namespace E213.Research.ModJoinExample

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat

/-- +2 step via L_6 then L_4: chain of length 2. -/
theorem mod_4_6_step_two {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N)
    (h6 : (leavesModNat 6).refines N)
    (r r' : Raw) (hdiff : Lens.leaves.view r' = Lens.leaves.view r + 2) :
    N.view r = N.view r' := by
  obtain ⟨w, hw⟩ := E213.Infinity.leaves_surjective_pos
    (Lens.leaves.view r + 6) (by omega)
  have h_r_w : (leavesModNat 6).view r = (leavesModNat 6).view w := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw]
    omega
  have h_w_r' : (leavesModNat 4).view w = (leavesModNat 4).view r' := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    omega
  exact (h6 _ _ h_r_w).trans (h4 _ _ h_w_r')

/-- Same leaves → same N-view (via L_4). -/
private theorem same_leaves_same_N {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N) (r r' : Raw)
    (hr : Lens.leaves.view r = Lens.leaves.view r') :
    N.view r = N.view r' := by
  apply h4
  show (leavesModNat 4).view r = (leavesModNat 4).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

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

/-- 일반 chain: +2k step. -/
theorem mod_4_6_step_2k {α : Type} (N : Lens α)
    (h4 : (leavesModNat 4).refines N)
    (h6 : (leavesModNat 6).refines N) (r : Raw) (k : Nat) :
    ∀ r', Lens.leaves.view r' = Lens.leaves.view r + 2 * k →
        N.view r = N.view r' := by
  induction k with
  | zero =>
      intro r' hr'
      apply same_leaves_same_N N h4
      omega
  | succ k ih =>
      intro r' hr'
      have h_r_ge := leaves_ge_one r
      obtain ⟨r'', hr''⟩ :=
        E213.Infinity.leaves_surjective_pos
          (Lens.leaves.view r + 2 * k) (by omega)
      have step1 : N.view r = N.view r'' := ih r'' hr''
      have step2 : N.view r'' = N.view r' := by
        apply mod_4_6_step_two N h4 h6 r'' r'
        omega
      exact step1.trans step2

end E213.Research.ModJoinExample
