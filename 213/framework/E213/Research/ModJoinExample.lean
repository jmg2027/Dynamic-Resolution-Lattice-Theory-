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
