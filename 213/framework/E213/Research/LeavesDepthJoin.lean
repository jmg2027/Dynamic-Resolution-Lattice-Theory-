import E213.Research.JoinEquiv

/-!
# Research.LeavesDepthJoin: leaves ⊔ depth ≠ constLens (비-mod non-trivial join)

`LeavesDepthIncomparable` 에서 leaves 와 depth 가 incomparable 임을
확인.  여기서 둘의 **join 이 universal 이 아님** 을 형식적으로
증명.

## 핵심 관찰

Raw.a (leaves=1, depth=0) 와 Raw.slash Raw.a Raw.b h (leaves=2,
depth=1) 는 JoinEquiv(leaves, depth) 에서 **분리된 class**.

## 증명 전략

Invariant `small r := Lens.leaves.view r = 1` 가 JoinEquiv 하에
preserved.

- ofL (leaves.equiv): same leaves, so same small-ness.
- ofM (depth.equiv): depth=0 ↔ leaves=1 ↔ small, so preserved.
- slash_cong: output 는 항상 Raw.slash (depth ≥ 1, leaves ≥ 2),
  never small.  양쪽 다 ¬ small, invariant holds vacuously.
- refl, symm, trans: 표준.

Raw.a 는 small, Raw.slash Raw.a Raw.b 는 not small.  따라서
JoinEquiv 로 분리.
-/

namespace E213.Research.LeavesDepthJoin

open E213.Firmware E213.Hypervisor E213.Research.JoinEquiv

/-- `small r` := r 가 base (Raw.a 또는 Raw.b), leaves=1. -/
private def small (r : Raw) : Prop := Lens.leaves.view r = 1

private theorem small_of_leaves_one {r : Raw} (h : Lens.leaves.view r = 1) : small r := h

private theorem leaves_of_small {r : Raw} (h : small r) : Lens.leaves.view r = 1 := h

/-- Leaves view 는 항상 ≥ 1. -/
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

/-- Raw.slash x y h 는 leaves ≥ 2 이므로 ¬ small. -/
private theorem not_small_slash (x y : Raw) (h : x ≠ y) :
    ¬ small (Raw.slash x y h) := by
  intro hsmall
  have hfs : Lens.leaves.view (Raw.slash x y h)
               = Lens.leaves.view x + Lens.leaves.view y := by
    apply Raw.fold_slash
    intro u v; exact Nat.add_comm u v
  have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
  have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
  have : Lens.leaves.view (Raw.slash x y h) ≥ 2 := by
    rw [hfs]; omega
  unfold small at hsmall
  omega

/-- Depth=0 iff small (= leaves=1 = base Raw.a/Raw.b). -/
private theorem small_iff_depth_zero (r : Raw) :
    small r ↔ Lens.depth.view r = 0 := by
  induction r using Raw.rec with
  | a => simp [small, Lens.leaves, Lens.depth, Lens.view, Raw.fold_a]
  | b => simp [small, Lens.leaves, Lens.depth, Lens.view, Raw.fold_b]
  | slash x y h _ _ =>
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hfsD : Lens.depth.view (Raw.slash x y h)
                    = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
        apply Raw.fold_slash
        intro u v
        show 1 + max u v = 1 + max v u
        rw [Nat.max_comm]
      have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
      have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
      constructor
      · intro hs
        unfold small at hs
        rw [hfsL] at hs
        omega
      · intro hd
        rw [hfsD] at hd
        omega

/-- **핵심 invariant**: `small r ↔ small r'` under JoinEquiv leaves depth. -/
theorem small_invariant (r r' : Raw)
    (h : JoinEquiv Lens.leaves Lens.depth r r') :
    small r ↔ small r' := by
  induction h with
  | ofL hrr' =>
      -- leaves.equiv: Lens.leaves.view r = Lens.leaves.view r'
      have : Lens.leaves.view _ = Lens.leaves.view _ := hrr'
      unfold small
      rw [this]
  | ofM hrr' =>
      have : Lens.depth.view _ = Lens.depth.view _ := hrr'
      rw [small_iff_depth_zero, small_iff_depth_zero, this]
  | refl x => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | slash_cong hxy hx'y' _ _ _ _ =>
      constructor
      · intro hs; exact absurd hs (not_small_slash _ _ hxy)
      · intro hs; exact absurd hs (not_small_slash _ _ hx'y')

/-- **Main 결과**: leaves ⊔ depth ≠ constLens (universal).
    Raw.a (leaves=1) 와 Raw.slash Raw.a Raw.b (leaves=2) 는
    JoinEquiv 분리.  즉 두 Lens 의 join 은 non-universal.  따라서
    비-mod family non-trivial (non-const) join 존재. -/
theorem leaves_depth_join_not_universal :
    ¬ JoinEquiv Lens.leaves Lens.depth Raw.a
        (Raw.slash Raw.a Raw.b (by decide)) := by
  intro h
  have := (small_invariant _ _ h).mp (by unfold small; rfl)
  exact not_small_slash _ _ _ this

/-- Raw.a 와 Raw.b 는 JoinEquiv 로 연결 (same leaves = 1). -/
theorem joinEquiv_a_b :
    JoinEquiv Lens.leaves Lens.depth Raw.a Raw.b := by
  apply JoinEquiv.ofL
  show Lens.leaves.view Raw.a = Lens.leaves.view Raw.b
  rfl

/-- small r → JoinEquiv r Raw.a (class of Raw.a 는 {Raw.a, Raw.b}
    를 포함). -/
theorem small_joinEquiv_a (r : Raw) (hs : small r) :
    JoinEquiv Lens.leaves Lens.depth r Raw.a := by
  apply JoinEquiv.ofL
  show Lens.leaves.view r = Lens.leaves.view Raw.a
  rw [leaves_of_small hs]
  rfl

/-- **Raw.a 의 class = {r : small r}**: leaves+depth JoinEquiv class
    of Raw.a 는 정확히 base Raws.  따라서 join 은 ≥ 2 non-trivial
    classes 를 가짐. -/
theorem class_of_a_iff_small (r : Raw) :
    JoinEquiv Lens.leaves Lens.depth Raw.a r ↔ small r := by
  constructor
  · intro h
    have := (small_invariant _ _ h).mp (by unfold small; rfl)
    exact this
  · intro hs
    exact JoinEquiv.symm (small_joinEquiv_a r hs)

end E213.Research.LeavesDepthJoin

namespace E213.Research.LeavesDepthJoin

open E213.Firmware E213.Hypervisor E213.Research.JoinEquiv

/-- 비-small 인 r 에 대해 leaves r = 2 → depth r = 1 (slash 의
    children 모두 small). -/
private theorem leaves_two_iff_depth_one (r : Raw) (hns : ¬ small r) :
    Lens.leaves.view r = 2 ↔ Lens.depth.view r = 1 := by
  induction r using Raw.rec with
  | a => exfalso; apply hns; unfold small; rfl
  | b => exfalso; apply hns; unfold small; rfl
  | slash x y h _ _ =>
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hfsD : Lens.depth.view (Raw.slash x y h)
                    = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
        apply Raw.fold_slash
        intro u v; show 1 + max u v = 1 + max v u; rw [Nat.max_comm]
      have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
      have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
      constructor
      · intro hl2
        rw [hfsL] at hl2
        -- leaves x + leaves y = 2 ∧ both ≥ 1 → both = 1 → both small → depth 0
        have hx1 : Lens.leaves.view x = 1 := by omega
        have hy1 : Lens.leaves.view y = 1 := by omega
        have hxd : Lens.depth.view x = 0 :=
          (small_iff_depth_zero x).mp hx1
        have hyd : Lens.depth.view y = 0 :=
          (small_iff_depth_zero y).mp hy1
        rw [hfsD, hxd, hyd]; rfl
      · intro hd1
        rw [hfsD] at hd1
        have hxd : Lens.depth.view x = 0 := by
          have : max (Lens.depth.view x) (Lens.depth.view y) = 0 := by omega
          omega
        have hyd : Lens.depth.view y = 0 := by
          have : max (Lens.depth.view x) (Lens.depth.view y) = 0 := by omega
          omega
        have hx1 : Lens.leaves.view x = 1 :=
          (small_iff_depth_zero x).mpr hxd
        have hy1 : Lens.leaves.view y = 1 :=
          (small_iff_depth_zero y).mpr hyd
        rw [hfsL, hx1, hy1]

/-- **Tier**: 0 (small/leaves=1), 1 (leaves=2), 2 (leaves≥3). -/
private def tier (r : Raw) : Nat :=
  if Lens.leaves.view r = 1 then 0
  else if Lens.leaves.view r = 2 then 1
  else 2

/-- depth ≥ 2 → leaves ≥ 3. -/
private theorem depth_ge_two_leaves_ge_three (r : Raw)
    (hd : Lens.depth.view r ≥ 2) : Lens.leaves.view r ≥ 3 := by
  induction r using Raw.rec with
  | a => unfold Lens.depth Lens.view at hd; simp [Raw.fold_a] at hd
  | b => unfold Lens.depth Lens.view at hd; simp [Raw.fold_b] at hd
  | slash x y h ihx ihy =>
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hfsD : Lens.depth.view (Raw.slash x y h)
                    = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
        apply Raw.fold_slash
        intro u v; show 1 + max u v = 1 + max v u; rw [Nat.max_comm]
      have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
      have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
      rw [hfsD] at hd
      -- max (depth x) (depth y) ≥ 1, so at least one ≥ 1
      by_cases hdx : Lens.depth.view x ≥ 1
      · by_cases hdx2 : Lens.depth.view x ≥ 2
        · have hxL : Lens.leaves.view x ≥ 3 := ihx hdx2
          rw [hfsL]; omega
        · -- depth x = 1, so leaves x ≥ 2
          have hdxe : Lens.depth.view x = 1 := by omega
          have hxns : ¬ small x := by
            intro hs
            have : Lens.depth.view x = 0 := (small_iff_depth_zero x).mp hs
            omega
          have hxL2 : Lens.leaves.view x = 2 :=
            (leaves_two_iff_depth_one x hxns).mpr hdxe
          rw [hfsL]; omega
      · have hdx0 : Lens.depth.view x = 0 := by omega
        have hxs : small x := (small_iff_depth_zero x).mpr hdx0
        have hxL1 : Lens.leaves.view x = 1 := leaves_of_small hxs
        -- max = depth y ≥ 1.  Subcase on depth y.
        have hdy1 : Lens.depth.view y ≥ 1 := by
          have : max (Lens.depth.view x) (Lens.depth.view y)
                  = Lens.depth.view y := by omega
          omega
        by_cases hdy2 : Lens.depth.view y ≥ 2
        · have hyL : Lens.leaves.view y ≥ 3 := ihy hdy2
          rw [hfsL]; omega
        · have hdye : Lens.depth.view y = 1 := by omega
          have hyns : ¬ small y := by
            intro hs
            have : Lens.depth.view y = 0 := (small_iff_depth_zero y).mp hs
            omega
          have hyL2 : Lens.leaves.view y = 2 :=
            (leaves_two_iff_depth_one y hyns).mpr hdye
          rw [hfsL]; omega

/-- tier 가 depth 에 의해 결정. -/
private theorem tier_eq_of_depth_eq (r r' : Raw)
    (h : Lens.depth.view r = Lens.depth.view r') : tier r = tier r' := by
  have hri : tier r = if Lens.depth.view r = 0 then 0
                     else if Lens.depth.view r = 1 then 1 else 2 := by
    unfold tier
    by_cases hd0 : Lens.depth.view r = 0
    · have hsm : small r := (small_iff_depth_zero r).mpr hd0
      have hl1 : Lens.leaves.view r = 1 := leaves_of_small hsm
      simp [hl1, hd0]
    · have hns : ¬ small r := fun hs =>
        hd0 ((small_iff_depth_zero r).mp hs)
      have hl_ne_1 : Lens.leaves.view r ≠ 1 := fun h => hns h
      by_cases hd1 : Lens.depth.view r = 1
      · have hl2 : Lens.leaves.view r = 2 :=
          (leaves_two_iff_depth_one r hns).mpr hd1
        simp [hl_ne_1, hl2, hd0, hd1]
      · have hd2 : Lens.depth.view r ≥ 2 := by
          have := Nat.zero_le (Lens.depth.view r); omega
        have hl3 : Lens.leaves.view r ≥ 3 :=
          depth_ge_two_leaves_ge_three r hd2
        have hl_ne_2 : Lens.leaves.view r ≠ 2 := by omega
        simp [hl_ne_1, hl_ne_2, hd0, hd1]
  have hri' : tier r' = if Lens.depth.view r' = 0 then 0
                       else if Lens.depth.view r' = 1 then 1 else 2 := by
    unfold tier
    by_cases hd0 : Lens.depth.view r' = 0
    · have hsm : small r' := (small_iff_depth_zero r').mpr hd0
      have hl1 : Lens.leaves.view r' = 1 := leaves_of_small hsm
      simp [hl1, hd0]
    · have hns : ¬ small r' := fun hs =>
        hd0 ((small_iff_depth_zero r').mp hs)
      have hl_ne_1 : Lens.leaves.view r' ≠ 1 := fun h => hns h
      by_cases hd1 : Lens.depth.view r' = 1
      · have hl2 : Lens.leaves.view r' = 2 :=
          (leaves_two_iff_depth_one r' hns).mpr hd1
        simp [hl_ne_1, hl2, hd0, hd1]
      · have hd2 : Lens.depth.view r' ≥ 2 := by
          have := Nat.zero_le (Lens.depth.view r'); omega
        have hl3 : Lens.leaves.view r' ≥ 3 :=
          depth_ge_two_leaves_ge_three r' hd2
        have hl_ne_2 : Lens.leaves.view r' ≠ 2 := by omega
        simp [hl_ne_1, hl_ne_2, hd0, hd1]
  rw [hri, hri', h]

/-- tier 가 leaves 에 의해 결정 (정의에서 직접). -/
private theorem tier_eq_of_leaves_eq (r r' : Raw)
    (h : Lens.leaves.view r = Lens.leaves.view r') : tier r = tier r' := by
  unfold tier; rw [h]

/-- slash 의 tier 는 양 child 가 모두 small (tier 0) 이면 1, 아니면 2. -/
private theorem tier_slash (x y : Raw) (h : x ≠ y) :
    tier (Raw.slash x y h) = (if tier x = 0 ∧ tier y = 0 then 1 else 2) := by
  have hfsL : Lens.leaves.view (Raw.slash x y h)
                = Lens.leaves.view x + Lens.leaves.view y := by
    apply Raw.fold_slash
    intro u v; exact Nat.add_comm u v
  have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
  have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
  have hslashL : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := hfsL
  unfold tier
  by_cases hsx : Lens.leaves.view x = 1
  · by_cases hsy : Lens.leaves.view y = 1
    · -- both small → output leaves = 2 → tier 1
      have hslash2 : Lens.leaves.view (Raw.slash x y h) = 2 := by
        rw [hfsL, hsx, hsy]
      have hslash_ne_1 : Lens.leaves.view (Raw.slash x y h) ≠ 1 := by
        rw [hslash2]; decide
      simp [hslash_ne_1, hslash2, hsx, hsy]
    · -- x small, y not small
      have hslash3 : Lens.leaves.view (Raw.slash x y h) ≥ 3 := by
        rw [hfsL, hsx]; omega
      have h_ne_1 : Lens.leaves.view (Raw.slash x y h) ≠ 1 := by omega
      have h_ne_2 : Lens.leaves.view (Raw.slash x y h) ≠ 2 := by omega
      have hty_ne_0 : ¬ ((if Lens.leaves.view y = 2 then 1 else 2 : Nat) = 0) := by
        split <;> decide
      simp [h_ne_1, h_ne_2, hsx, hsy, hty_ne_0]
  · by_cases hsy : Lens.leaves.view y = 1
    · have hslash3 : Lens.leaves.view (Raw.slash x y h) ≥ 3 := by
        have : Lens.leaves.view x ≥ 2 := by omega
        rw [hfsL, hsy]; omega
      have h_ne_1 : Lens.leaves.view (Raw.slash x y h) ≠ 1 := by omega
      have h_ne_2 : Lens.leaves.view (Raw.slash x y h) ≠ 2 := by omega
      have htx_ne_0 : ¬ ((if Lens.leaves.view x = 2 then 1 else 2 : Nat) = 0) := by
        split <;> decide
      simp [h_ne_1, h_ne_2, hsx, hsy, htx_ne_0]
    · have hslash4 : Lens.leaves.view (Raw.slash x y h) ≥ 4 := by
        have : Lens.leaves.view x ≥ 2 := by omega
        have : Lens.leaves.view y ≥ 2 := by omega
        rw [hfsL]; omega
      have h_ne_1 : Lens.leaves.view (Raw.slash x y h) ≠ 1 := by omega
      have h_ne_2 : Lens.leaves.view (Raw.slash x y h) ≠ 2 := by omega
      have htx_ne_0 : ¬ ((if Lens.leaves.view x = 2 then 1 else 2 : Nat) = 0) := by
        split <;> decide
      simp [h_ne_1, h_ne_2, hsx, hsy, htx_ne_0]

/-- slash_cong 단계: tier 의 join_cong-like 보존. -/
private theorem tier_slash_from_inputs (x y x' y' : Raw)
    (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (htx : tier x = tier x') (hty : tier y = tier y') :
    tier (Raw.slash x y hxy) = tier (Raw.slash x' y' hx'y') := by
  rw [tier_slash, tier_slash, htx, hty]

end E213.Research.LeavesDepthJoin

namespace E213.Research.LeavesDepthJoin

open E213.Firmware E213.Hypervisor E213.Research.JoinEquiv

/-- **Tier invariant**: JoinEquiv leaves depth 하에 tier 는 보존. -/
theorem tier_invariant (r r' : Raw)
    (h : JoinEquiv Lens.leaves Lens.depth r r') : tier r = tier r' := by
  induction h with
  | ofL hrr' =>
      have : Lens.leaves.view _ = Lens.leaves.view _ := hrr'
      exact tier_eq_of_leaves_eq _ _ this
  | ofM hrr' =>
      have : Lens.depth.view _ = Lens.depth.view _ := hrr'
      exact tier_eq_of_depth_eq _ _ this
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | slash_cong hxy hx'y' _ _ ih1 ih2 =>
      exact tier_slash_from_inputs _ _ _ _ hxy hx'y' ih1 ih2

end E213.Research.LeavesDepthJoin

namespace E213.Research.LeavesDepthJoin

open E213.Firmware E213.Hypervisor E213.Research.JoinEquiv

/-- 구체 Raws: tier 0, 1, 2 의 대표. -/
private def repr0 : Raw := Raw.a
private def repr1 : Raw := Raw.slash Raw.a Raw.b (by decide)
private def repr2 : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

private theorem repr0_tier : tier repr0 = 0 := by
  unfold tier repr0; rfl

private theorem repr1_tier : tier repr1 = 1 := by
  unfold tier repr1
  have h : Lens.leaves.view (Raw.slash Raw.a Raw.b (by decide : (Raw.a : Raw) ≠ Raw.b)) = 2 := by
    have hfs : Lens.leaves.view (Raw.slash Raw.a Raw.b (by decide))
                  = Lens.leaves.view Raw.a + Lens.leaves.view Raw.b := by
      apply Raw.fold_slash
      intro u v; exact Nat.add_comm u v
    rw [hfs]; rfl
  rw [h]; rfl

private theorem repr2_tier : tier repr2 = 2 := by
  unfold tier repr2
  have h2 : Lens.leaves.view (Raw.slash Raw.a Raw.b (by decide : (Raw.a : Raw) ≠ Raw.b)) = 2 := by
    have hfs : Lens.leaves.view (Raw.slash Raw.a Raw.b (by decide))
                  = Lens.leaves.view Raw.a + Lens.leaves.view Raw.b := by
      apply Raw.fold_slash
      intro u v; exact Nat.add_comm u v
    rw [hfs]; rfl
  have h3 : Lens.leaves.view
              (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide))
                (by decide : Raw.a ≠ Raw.slash Raw.a Raw.b _))
            = 3 := by
    have hfs : Lens.leaves.view
                 (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide))
                = Lens.leaves.view Raw.a
                  + Lens.leaves.view (Raw.slash Raw.a Raw.b (by decide)) := by
      apply Raw.fold_slash
      intro u v; exact Nat.add_comm u v
    rw [hfs, h2]; rfl
  rw [h3]; rfl

/-- **3 classes 분리**: repr0 (small), repr1 ((2,1)), repr2 (≥3 leaves)
    는 JoinEquiv leaves depth 에서 모두 서로 분리. -/
theorem three_classes_distinct :
    (¬ JoinEquiv Lens.leaves Lens.depth repr0 repr1) ∧
    (¬ JoinEquiv Lens.leaves Lens.depth repr1 repr2) ∧
    (¬ JoinEquiv Lens.leaves Lens.depth repr0 repr2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := tier_invariant _ _ h
    rw [repr0_tier, repr1_tier] at this
    exact absurd this (by decide)
  · intro h
    have := tier_invariant _ _ h
    rw [repr1_tier, repr2_tier] at this
    exact absurd this (by decide)
  · intro h
    have := tier_invariant _ _ h
    rw [repr0_tier, repr2_tier] at this
    exact absurd this (by decide)

end E213.Research.LeavesDepthJoin
