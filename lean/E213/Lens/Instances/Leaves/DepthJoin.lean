import E213.Lens.Lattice.JoinEquiv

/-!
# LeavesDepthJoin: leaves ⊔ depth ≠ constLens (non-trivial non-mod join)

`LeavesDepthIncomparable` confirmed that leaves and depth are
incomparable.  Here we formally prove that their **join is not
universal**.

## Core Observation

Raw.a (leaves=1, depth=0) and Raw.slash Raw.a Raw.b h (leaves=2,
depth=1) are **separated classes** in JoinEquiv(leaves, depth).

## Proof Strategy

The invariant `small r := Lens.leaves.view r = 1` is preserved
under JoinEquiv.

- ofL (leaves.equiv): same leaves, so same small-ness.
- ofM (depth.equiv): depth=0 ↔ leaves=1 ↔ small, so preserved.
- slash_cong: output is always Raw.slash (depth ≥ 1, leaves ≥ 2),
  never small.  Both sides ¬ small, invariant holds vacuously.
- refl, symm, trans: standard.

Raw.a is small; Raw.slash Raw.a Raw.b is not small.  Therefore
they are separated by JoinEquiv.
-/

namespace E213.Lens.Instances.Leaves.DepthJoin

open E213.Theory E213.Lens E213.Lens.Lattice.JoinEquiv

/-- `small r` := r is a base (Raw.a or Raw.b), leaves=1. -/
private def small (r : Raw) : Prop := Lens.leaves.view r = 1

private theorem small_of_leaves_one {r : Raw} (h : Lens.leaves.view r = 1) : small r := h

private theorem leaves_of_small {r : Raw} (h : small r) : Lens.leaves.view r = 1 := h

/-- Leaves view is always ≥ 1. -/
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

/-- Raw.slash x y h has leaves ≥ 2, so ¬ small. -/
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

/-- **Core invariant**: `small r ↔ small r'` under JoinEquiv leaves depth. -/
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

/-- **Main result**: leaves ⊔ depth ≠ constLens (universal).
    Raw.a (leaves=1) and Raw.slash Raw.a Raw.b (leaves=2) are
    separated by JoinEquiv.  Thus the join of the two Lenses is
    non-universal.  Therefore a non-trivial (non-const) join of a
    non-mod family exists. -/
theorem leaves_depth_join_not_universal :
    ¬ JoinEquiv Lens.leaves Lens.depth Raw.a
        (Raw.slash Raw.a Raw.b (by decide)) := by
  intro h
  have := (small_invariant _ _ h).mp (by unfold small; rfl)
  exact not_small_slash _ _ _ this

/-- Raw.a and Raw.b are connected by JoinEquiv (same leaves = 1). -/
theorem joinEquiv_a_b :
    JoinEquiv Lens.leaves Lens.depth Raw.a Raw.b := by
  apply JoinEquiv.ofL
  show Lens.leaves.view Raw.a = Lens.leaves.view Raw.b
  rfl

/-- small r → JoinEquiv r Raw.a (the class of Raw.a contains
    {Raw.a, Raw.b}). -/
theorem small_joinEquiv_a (r : Raw) (hs : small r) :
    JoinEquiv Lens.leaves Lens.depth r Raw.a := by
  apply JoinEquiv.ofL
  show Lens.leaves.view r = Lens.leaves.view Raw.a
  rw [leaves_of_small hs]
  rfl

/-- **Class of Raw.a = {r : small r}**: the leaves+depth JoinEquiv
    class of Raw.a is exactly the base Raws.  Therefore the join has
    ≥ 2 non-trivial classes. -/
theorem class_of_a_iff_small (r : Raw) :
    JoinEquiv Lens.leaves Lens.depth Raw.a r ↔ small r := by
  constructor
  · intro h
    have := (small_invariant _ _ h).mp (by unfold small; rfl)
    exact this
  · intro hs
    exact JoinEquiv.symm (small_joinEquiv_a r hs)



/-- For non-small r: leaves r = 2 → depth r = 1 (all children of
    the slash are small). -/
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

/-- tier is determined by depth. -/
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

/-- tier is determined by leaves (directly from the definition). -/
private theorem tier_eq_of_leaves_eq (r r' : Raw)
    (h : Lens.leaves.view r = Lens.leaves.view r') : tier r = tier r' := by
  unfold tier; rw [h]

/-- tier of a slash is 1 if both children are small (tier 0), else 2. -/
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

/-- slash_cong step: join_cong-like preservation of tier. -/
private theorem tier_slash_from_inputs (x y x' y' : Raw)
    (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (htx : tier x = tier x') (hty : tier y = tier y') :
    tier (Raw.slash x y hxy) = tier (Raw.slash x' y' hx'y') := by
  rw [tier_slash, tier_slash, htx, hty]



/-- **Tier invariant**: tier is preserved under JoinEquiv leaves depth. -/
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


open E213.Theory E213.Lens

/-- **tierLens**: concrete common upper bound of leaves and depth.
    view = tier r ∈ {0, 1, 2}. -/
def tierLens : Lens Nat where
  base_a := 0
  base_b := 0
  combine := fun u v => if u = 0 ∧ v = 0 then 1 else 2

private theorem tierLens_combine_sym (u v : Nat) :
    tierLens.combine u v = tierLens.combine v u := by
  show (if u = 0 ∧ v = 0 then 1 else 2)
       = (if v = 0 ∧ u = 0 then 1 else 2)
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · simp [hu, hv]
    · simp [hu, hv]
  · simp [hu]

/-- tierLens.view = tier function.  Represented as Nat in Bool-style. -/
theorem tierLens_view_eq_tier (r : Raw) : tierLens.view r = tier r := by
  induction r using Raw.rec with
  | a => unfold tier tierLens; show 0 = (if Lens.leaves.view Raw.a = 1 then 0 else _); rfl
  | b => unfold tier tierLens; show 0 = (if Lens.leaves.view Raw.b = 1 then 0 else _); rfl
  | slash x y h ihx ihy =>
      have hfs : tierLens.view (Raw.slash x y h)
                   = tierLens.combine (tierLens.view x) (tierLens.view y) := by
        apply Raw.fold_slash
        intro u v; exact tierLens_combine_sym u v
      rw [hfs, ihx, ihy, tier_slash]
      show (if tier x = 0 ∧ tier y = 0 then 1 else 2)
           = (if tier x = 0 ∧ tier y = 0 then 1 else 2)
      rfl



/-- Concrete Raws: representatives of tiers 0, 1, 2. -/
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

/-- **3 classes separated**: repr0 (small), repr1 ((2,1)), repr2 (≥3 leaves)
    are all mutually separated in JoinEquiv leaves depth. -/
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



/-- **leaves refines tierLens** (tierLens is an upper bound of leaves). -/
theorem leaves_refines_tierLens : Lens.leaves.refines tierLens := by
  intro r r' h
  show tierLens.view r = tierLens.view r'
  rw [tierLens_view_eq_tier, tierLens_view_eq_tier]
  exact tier_eq_of_leaves_eq r r' h

/-- **depth refines tierLens** (tierLens is an upper bound of depth). -/
theorem depth_refines_tierLens : Lens.depth.refines tierLens := by
  intro r r' h
  show tierLens.view r = tierLens.view r'
  rw [tierLens_view_eq_tier, tierLens_view_eq_tier]
  exact tier_eq_of_depth_eq r r' h

/-- **tierLens.view takes exactly 3 values** (all of 0, 1, 2 are hit). -/
theorem tierLens_three_values :
    tierLens.view repr0 = 0 ∧
    tierLens.view repr1 = 1 ∧
    tierLens.view repr2 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tierLens_view_eq_tier]; exact repr0_tier
  · rw [tierLens_view_eq_tier]; exact repr1_tier
  · rw [tierLens_view_eq_tier]; exact repr2_tier

/-- **JoinEquiv leaves depth ⊆ tierLens.equiv** (direct consequence
    of the universal property: tierLens is an upper bound). -/
theorem joinEquiv_subset_tierLens (r r' : Raw)
    (h : JoinEquiv Lens.leaves Lens.depth r r') :
    tierLens.equiv r r' := by
  show tierLens.view r = tierLens.view r'
  rw [tierLens_view_eq_tier, tierLens_view_eq_tier]
  exact tier_invariant r r' h

end E213.Lens.Instances.Leaves.DepthJoin
