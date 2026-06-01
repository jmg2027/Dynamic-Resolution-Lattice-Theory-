import E213.Lens.Lattice.JoinEquiv
import E213.Meta.Tactic.NatHelper

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
open E213.Tactic.NatHelper

/-- `small r` := r is a base (Raw.a or Raw.b), leaves=1. -/
private def small (r : Raw) : Prop := Lens.leaves.view r = 1

private theorem small_of_leaves_one {r : Raw} (h : Lens.leaves.view r = 1) : small r := h

private theorem leaves_of_small {r : Raw} (h : small r) : Lens.leaves.view r = 1 := h

private theorem leaves_ge_one (r : Raw) : 1 ≤ Lens.leaves.view r :=
  Lens.leaves_view_ge_one r

/-- Raw.slash x y h has leaves ≥ 2, so ¬ small.  (The general Nat/`max`
    micro-lemmas this argument needs live in `Meta/Tactic/NatHelper`.) -/
private theorem not_small_slash (x y : Raw) (h : x ≠ y) :
    ¬ small (Raw.slash x y h) := by
  intro hsmall
  have hfs : Lens.leaves.view (Raw.slash x y h)
               = Lens.leaves.view x + Lens.leaves.view y := by
    apply Raw.fold_slash
    intro u v; exact Nat.add_comm u v
  have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
  have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
  have hge : Lens.leaves.view (Raw.slash x y h) ≥ 2 := by
    rw [hfs]; exact two_le_add hxge hyge
  unfold small at hsmall
  exact absurd (hsmall ▸ hge) (by decide)

/-- Depth=0 iff small (= leaves=1 = base Raw.a/Raw.b). -/
private theorem small_iff_depth_zero (r : Raw) :
    small r ↔ Lens.depth.view r = 0 := by
  induction r using Raw.rec with
  | a =>
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> rfl
  | b =>
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> rfl
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
        rw [E213.Tactic.NatHelper.max_comm]
      have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
      have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
      refine ⟨fun hs => ?_, fun hd => ?_⟩
      · -- small slash → contradiction: leaves(slash) ≥ 2 ≠ 1
        unfold small at hs
        rw [hfsL] at hs
        -- hs : Lens.leaves.view x + Lens.leaves.view y = 1
        -- but x ≥ 1 and y ≥ 1 → sum ≥ 2.  Constructive Nat contradiction.
        exact absurd hs (by
          intro heq
          have h2 : 2 ≤ Lens.leaves.view x + Lens.leaves.view y :=
            Nat.add_le_add hxge hyge
          have : (2 : Nat) ≤ 1 := heq ▸ h2
          exact Nat.not_succ_le_self 1 this)
      · -- 1 + max d_x d_y = 0 → contradiction.
        rw [hfsD] at hd
        -- 1 ≤ 1 + n, but hd says 1 + n = 0, so 1 ≤ 0, impossible.
        have h1 : 1 ≤ 1 + max (Lens.depth.view x) (Lens.depth.view y) :=
          Nat.le_add_right 1 _
        rw [hd] at h1
        exact absurd h1 (Nat.not_succ_le_zero 0)

/-- **Core invariant**: `small r ↔ small r'` under JoinEquiv leaves depth. -/
theorem small_invariant (r r' : Raw)
    (h : JoinEquiv Lens.leaves Lens.depth r r') :
    small r ↔ small r' := by
  induction h with
  | ofL hrr' =>
      -- leaves.equiv: Lens.leaves.view r = Lens.leaves.view r'.  Transport `small`
      -- (= `leaves = 1`) across the Eq with `▸` — no `rw`-on-`Iff` propext.
      have hl : Lens.leaves.view _ = Lens.leaves.view _ := hrr'
      exact ⟨fun hh => hl.symm.trans hh, fun hh => hl.trans hh⟩
  | ofM hrr' =>
      have hd : Lens.depth.view _ = Lens.depth.view _ := hrr'
      have hmid : (Lens.depth.view _ = 0) ↔ (Lens.depth.view _ = 0) :=
        ⟨fun hh => hd.symm.trans hh, fun hh => hd.trans hh⟩
      exact (small_iff_depth_zero _).trans (hmid.trans (small_iff_depth_zero _).symm)
  | refl x => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | slash_cong hxy hx'y' _ _ _ _ =>
      exact ⟨fun hs => absurd hs (not_small_slash _ _ hxy),
             fun hs => absurd hs (not_small_slash _ _ hx'y')⟩

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
        intro u v; show 1 + max u v = 1 + max v u; rw [E213.Tactic.NatHelper.max_comm]
      have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
      have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
      constructor
      · intro hl2
        rw [hfsL] at hl2
        -- leaves x + leaves y = 2 ∧ both ≥ 1 → both = 1 → both small → depth 0
        obtain ⟨hx1, hy1⟩ := eq_one_of_add_eq_two hxge hyge hl2
        have hxd : Lens.depth.view x = 0 :=
          (small_iff_depth_zero x).mp hx1
        have hyd : Lens.depth.view y = 0 :=
          (small_iff_depth_zero y).mp hy1
        rw [hfsD, hxd, hyd]; rfl
      · intro hd1
        rw [hfsD] at hd1
        -- 1 + max dx dy = 1 → max dx dy = 0 → dx = dy = 0
        have hd1' : 1 + max (Lens.depth.view x) (Lens.depth.view y) = 1 + 0 := hd1
        have hmax0 : max (Lens.depth.view x) (Lens.depth.view y) = 0 :=
          E213.Tactic.NatHelper.add_left_cancel hd1'
        obtain ⟨hxd, hyd⟩ := max_eq_zero hmax0
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

/-- `1 ≤ depth r → 2 ≤ leaves r` (non-base ⇒ at least two leaves). -/
private theorem two_le_leaves_of_depth_ge_one (r : Raw)
    (hd : 1 ≤ Lens.depth.view r) : 2 ≤ Lens.leaves.view r := by
  have hne1 : Lens.leaves.view r ≠ 1 := by
    intro he
    have hd0 : Lens.depth.view r = 0 := (small_iff_depth_zero r).mp he
    exact absurd (hd0 ▸ hd) (by decide)
  exact two_le_of_ne_one (leaves_ge_one r) hne1

/-- depth ≥ 2 → leaves ≥ 3.  One child has depth ≥ 1 (so ≥ 2 leaves); the
    other has ≥ 1 leaf; the slash sums them. -/
private theorem depth_ge_two_leaves_ge_three (r : Raw)
    (hd : Lens.depth.view r ≥ 2) : Lens.leaves.view r ≥ 3 := by
  induction r using Raw.rec with
  | a => exact absurd hd (by decide)
  | b => exact absurd hd (by decide)
  | slash x y h _ _ =>
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hfsD : Lens.depth.view (Raw.slash x y h)
                    = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
        apply Raw.fold_slash
        intro u v; show 1 + max u v = 1 + max v u; rw [E213.Tactic.NatHelper.max_comm]
      have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
      have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
      rw [hfsD] at hd
      have hd' : 1 + 1 ≤ 1 + max (Lens.depth.view x) (Lens.depth.view y) := hd
      have hmax1 : 1 ≤ max (Lens.depth.view x) (Lens.depth.view y) :=
        E213.Tactic.NatHelper.le_of_add_le_add_left hd'
      rw [hfsL]
      rcases or_ge_one_of_max_ge_one hmax1 with hgx | hgy
      · exact Nat.add_le_add (two_le_leaves_of_depth_ge_one x hgx) hyge
      · exact Nat.add_le_add hxge (two_le_leaves_of_depth_ge_one y hgy)

/-- tier is determined by depth. -/
private theorem tier_eq_of_depth_eq (r r' : Raw)
    (h : Lens.depth.view r = Lens.depth.view r') : tier r = tier r' := by
  have hri : ∀ s : Raw, tier s = if Lens.depth.view s = 0 then 0
                     else if Lens.depth.view s = 1 then 1 else 2 := by
    intro s
    unfold tier
    by_cases hd0 : Lens.depth.view s = 0
    · have hl1 : Lens.leaves.view s = 1 :=
        leaves_of_small ((small_iff_depth_zero s).mpr hd0)
      rw [if_pos hl1, if_pos hd0]
    · have hns : ¬ small s := fun hs => hd0 ((small_iff_depth_zero s).mp hs)
      have hl_ne_1 : Lens.leaves.view s ≠ 1 := fun he => hns he
      by_cases hd1 : Lens.depth.view s = 1
      · have hl2 : Lens.leaves.view s = 2 :=
          (leaves_two_iff_depth_one s hns).mpr hd1
        rw [if_neg hl_ne_1, if_pos hl2, if_neg hd0, if_pos hd1]
      · have hl3 : Lens.leaves.view s ≥ 3 :=
          depth_ge_two_leaves_ge_three s (ge_two_of_ne_zero_ne_one hd0 hd1)
        have hl_ne_2 : Lens.leaves.view s ≠ 2 := fun he => absurd (he ▸ hl3) (by decide)
        rw [if_neg hl_ne_1, if_neg hl_ne_2, if_neg hd0, if_neg hd1]
  rw [hri r, hri r', h]

/-- tier is determined by leaves (directly from the definition). -/
private theorem tier_eq_of_leaves_eq (r r' : Raw)
    (h : Lens.leaves.view r = Lens.leaves.view r') : tier r = tier r' := by
  unfold tier; rw [h]

/-- `leaves r = 1 → tier r = 0`. -/
private theorem tier_zero_of_leaves_one (r : Raw) (h : Lens.leaves.view r = 1) :
    tier r = 0 := by unfold tier; rw [if_pos h]

/-- `leaves r ≠ 1 → tier r ≠ 0`. -/
private theorem tier_ne_zero_of_leaves_ne_one (r : Raw) (h : Lens.leaves.view r ≠ 1) :
    tier r ≠ 0 := by
  unfold tier; rw [if_neg h]
  by_cases h2 : Lens.leaves.view r = 2
  · rw [if_pos h2]; decide
  · rw [if_neg h2]; decide

/-- `leaves r = 2 → tier r = 1`. -/
private theorem tier_one_of_leaves_two (r : Raw) (h : Lens.leaves.view r = 2) :
    tier r = 1 := by
  have hne1 : Lens.leaves.view r ≠ 1 := by rw [h]; decide
  unfold tier; rw [if_neg hne1, if_pos h]

/-- `leaves r ≥ 3 → tier r = 2`. -/
private theorem tier_two_of_leaves_ge_three (r : Raw) (h : Lens.leaves.view r ≥ 3) :
    tier r = 2 := by
  have hne1 : Lens.leaves.view r ≠ 1 := fun he => absurd (he ▸ h) (by decide)
  have hne2 : Lens.leaves.view r ≠ 2 := fun he => absurd (he ▸ h) (by decide)
  unfold tier; rw [if_neg hne1, if_neg hne2]

/-- tier of a slash is 1 if both children are small (tier 0), else 2. -/
private theorem tier_slash (x y : Raw) (h : x ≠ y) :
    tier (Raw.slash x y h) = (if tier x = 0 ∧ tier y = 0 then 1 else 2) := by
  have hfsL : Lens.leaves.view (Raw.slash x y h)
                = Lens.leaves.view x + Lens.leaves.view y :=
    Raw.fold_slash _ _ _ (fun u v => Nat.add_comm u v) x y h
  have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
  have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
  by_cases hsx : Lens.leaves.view x = 1
  · by_cases hsy : Lens.leaves.view y = 1
    · -- both small → output leaves = 2 → tier 1; both tiers 0 → RHS 1
      have hslash2 : Lens.leaves.view (Raw.slash x y h) = 2 := by rw [hfsL, hsx, hsy]
      rw [tier_one_of_leaves_two _ hslash2,
          if_pos ⟨tier_zero_of_leaves_one x hsx, tier_zero_of_leaves_one y hsy⟩]
    · -- y not small → leaves slash ≥ 3 → tier 2; tier y ≠ 0 → RHS 2
      have hslash3 : Lens.leaves.view (Raw.slash x y h) ≥ 3 := by
        rw [hfsL, hsx]; exact Nat.add_le_add (Nat.le_refl 1) (two_le_of_ne_one hyge hsy)
      rw [tier_two_of_leaves_ge_three _ hslash3,
          if_neg (fun hc => tier_ne_zero_of_leaves_ne_one y hsy hc.2)]
  · by_cases hsy : Lens.leaves.view y = 1
    · have hslash3 : Lens.leaves.view (Raw.slash x y h) ≥ 3 := by
        rw [hfsL, hsy]; exact Nat.add_le_add (two_le_of_ne_one hxge hsx) (Nat.le_refl 1)
      rw [tier_two_of_leaves_ge_three _ hslash3,
          if_neg (fun hc => tier_ne_zero_of_leaves_ne_one x hsx hc.1)]
    · have hslash3 : Lens.leaves.view (Raw.slash x y h) ≥ 3 := by
        rw [hfsL]
        exact Nat.le_trans (by decide : (3 : Nat) ≤ 2 + 2)
          (Nat.add_le_add (two_le_of_ne_one hxge hsx) (two_le_of_ne_one hyge hsy))
      rw [tier_two_of_leaves_ge_three _ hslash3,
          if_neg (fun hc => tier_ne_zero_of_leaves_ne_one x hsx hc.1)]

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
    · rw [if_pos ⟨hu, hv⟩, if_pos ⟨hv, hu⟩]
    · rw [if_neg (fun hc => hv hc.2), if_neg (fun hc => hv hc.1)]
  · rw [if_neg (fun hc => hu hc.1), if_neg (fun hc => hu hc.2)]

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
