# Cluster `equality_rw` — 377 decls (sample limited to 50)

(Auto-extracted by `tools/theorem_inspect.py`.)

## `Tree` (E213/Firmware/Raw/Cmp.lean)

```lean
theorem Tree.cmp_eq_iff (x y : Tree) : Tree.cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | a => cases y <;> simp [Tree.cmp]
  | b => cases y <;> simp [Tree.cmp]
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => simp [Tree.cmp]
      | b => simp [Tree.cmp]
      | slash x₂ y₂ =>
          simp only [Tree.cmp]
          constructor
          · intro h
            split at h <;> rename_i hc
            · rw [(ihy y₂).mp h, show x₁ = x₂ from (ihx x₂).mp hc]
            all_goals cases h
          · intro h
            injection h with hx hy
            rw [← hx, ← hy]
 
... [truncated]
```

## `canonicalBy_Tree_cmp` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem canonicalBy_Tree_cmp (t : Tree) :
    canonicalBy Tree.cmp t = t.canonical := by
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      unfold canonicalBy Tree.canonical
      rw [ihx, ihy]
      rfl

/-- Therefore the underlying predicate of RawBy Tree.cmp = Tree.canonical. -/
```

## `slashTree_comm` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem slashTree_comm (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : Tree) (hxy : x ≠ y) :
    slashTree cmp x y = slashTree cmp y x := by
  have hsw := h.swap x y
  unfold slashTree
  cases hxy_cmp : cmp x y with
  | lt =>
      have hyx_cmp : cmp y x = .gt := by
        rw [hxy_cmp] at hsw
        cases hyx_val : cmp y x with
        | lt => rw [hyx_val] at hsw; cases hsw
        | eq => rw [hyx_val] at hsw; cases hsw
        | gt => rfl
      rw [hyx_cmp]
  | eq =>
      have hxy_val : x = y := (h.eq_iff x y).mp hxy_cmp
      exact absurd hxy_val hxy
  | gt =>
      have hyx_
... [truncated]
```

## `RawBy_slash_val` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem RawBy_slash_val (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : RawBy cmp) (hxy : x ≠ y) :
    (RawBy.slash cmp h x y hxy).val = slashTree cmp x.val y.val := by
  unfold RawBy.slash slashTree
  split
  · rename_i hc
    show x.val.slash y.val = (match cmp x.val y.val with
      | .lt => x.val.slash y.val
      | .gt => y.val.slash x.val
      | .eq => x.val.slash y.val)
    rw [hc]
  · rename_i hc
    show y.val.slash x.val = (match cmp x.val y.val with
      | .lt => x.val.slash y.val
      | .gt => y.val.slash x.val
      | .eq => x.val.slash y.val)
    rw [hc]
  · renam
... [truncated]
```

## `RawBy` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
def RawBy (cmp : Tree → Tree → Ordering) : Type :=
  { t : Tree // canonicalBy cmp t = true }

/-- When using the original Tree.cmp, canonicalBy = Tree.canonical. -/
```

## `canonicalBy_slash_lt` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem canonicalBy_slash_lt {cmp : Tree → Tree → Ordering}
    {x y : Tree} (h : canonicalBy cmp (.slash x y) = true) :
    cmp x y = .lt := by
  unfold canonicalBy at h
  rw [Bool.and_eq_true] at h
  obtain ⟨_, hlt_raw⟩ := h
  match hm : cmp x y with
  | .lt => rfl
  | .eq => rw [hm] at hlt_raw; cases hlt_raw
  | .gt => rw [hm] at hlt_raw; cases hlt_raw
```

## `Raw` (E213/Firmware/Raw/Slash.lean)

```lean
def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            unfold Tree.canonical
            rw [x.property, y.property, hc]; rfl⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
              Tree.cmp_gt_to_lt_swap x.val y.val hc
            unfold Tree.canonical
            rw [y.property, x.property, hlt]; rfl⟩
  | .eq => absurd (Tree.cmp_eq_to_eq _ _ hc)
            (fun e => h (Subtype.ext e))
```

## `Tree` (E213/Firmware/Raw/Swap.lean)

```lean
def Tree.swap : Tree → Tree
  | .a         => .b
  | .b         => .a
  | .slash x y =>
      let x' := Tree.swap x
      let y' := Tree.swap y
      match Tree.cmp x' y' with
      | .lt => .slash x' y'
      | .gt => .slash y' x'
      | .eq => x'
```

## `Raw` (E213/Firmware/Raw/Swap.lean)

```lean
def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩
```

## `Raw` (E213/Firmware/Raw/SwapSlash.lean)

```lean
theorem Raw.swap_slash (x y : Raw) (h : x ≠ y) :
    Raw.swap (Raw.slash x y h)
      = Raw.slash (Raw.swap x) (Raw.swap y)
          (fun e => h (Raw.swap_injective e)) := by
  apply Subtype.ext
  unfold Raw.slash Raw.swap
  split <;> rename_i hLcmp
  · -- cmp x.val y.val = .lt
    split <;> rename_i hRcmp
    · -- cmp (swap x.val) (swap y.val) = .lt
      show Tree.swap (.slash x.val y.val) = .slash (Tree.swap x.val) (Tree.swap y.val)
      simp only [Tree.swap, hRcmp]
    · -- cmp (swap x.val)(swap y.val) = .gt
      show Tree.swap (.slash x.val y.val) = .slash (Tree.swap y.val) (Tree.swap 
... [truncated]
```

## `depth_swap_invariant` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
theorem depth_swap_invariant (r : Raw) :
    Lens.depth.view (Raw.swap r) = Lens.depth.view r := by
  show Raw.fold 0 0 (fun a b => 1 + max a b) (Raw.swap r)
     = Raw.fold 0 0 (fun a b => 1 + max a b) r
  rw [Raw.fold_eq_depth, Raw.fold_eq_depth, Raw.swap_depth]

/-- **Leaves lens is swap-blind.** Same base value for `a` and
    `b`. The Lens counts size, erasing identity. -/
```

## `leaves_swap_invariant` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
theorem leaves_swap_invariant (r : Raw) :
    Lens.leaves.view (Raw.swap r) = Lens.leaves.view r := by
  show Raw.fold 1 1 (· + ·) (Raw.swap r) = Raw.fold 1 1 (· + ·) r
  rw [Raw.fold_eq_leaves, Raw.fold_eq_leaves, Raw.swap_leaves]
```

## `R4_conj_agrees_on_image` (E213/Hypervisor/Lens/Characterisation/Core.lean)

```lean
theorem R4_conj_agrees_on_image
    {α : Type} {L : Hypervisor.Lens α} {conj1 conj2 : α → α}
    (h1 : SwapMatching L conj1) (h2 : SwapMatching L conj2)
    (r : Raw) : conj1 (L.view r) = conj2 (L.view r) := by
  have e1 := h1.2.2 r
  have e2 := h2.2.2 r
  rw [← e1, ← e2]

/-- **R4 uniqueness on surjective Lenses.**  If `view` is
    surjective and two involutions both witness R4, they are
    equal as functions. -/
```

## `R4_conj_unique_of_surjective` (E213/Hypervisor/Lens/Characterisation/Core.lean)

```lean
theorem R4_conj_unique_of_surjective
    {α : Type} {L : Hypervisor.Lens α} {conj1 conj2 : α → α}
    (h1 : SwapMatching L conj1) (h2 : SwapMatching L conj2)
    (hsurj : Function.Surjective L.view) : conj1 = conj2 := by
  funext u
  obtain ⟨r, hr⟩ := hsurj u
  have := R4_conj_agrees_on_image h1 h2 r
  rw [hr] at this
  exact this
```

## `composite_a` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem composite_a : composite Raw.a = constTrueLens := by
  unfold composite
  rw [@universalMorphism_a Bool boolXorHasDistinguishing]
  rfl
```

## `composite_b` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem composite_b : composite Raw.b = constFalseLens := by
  unfold composite
  rw [@universalMorphism_b Bool boolXorHasDistinguishing]
  rfl
```

## `composite_slash` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem composite_slash (x y : Raw) (h : x ≠ y) :
    composite (Raw.slash x y h) = lensXor (composite x) (composite y) := by
  unfold composite
  rw [@universalMorphism_slash Bool boolXorHasDistinguishing x y h]
  exact boolToConstLens_xor _ _
```

## `constComposite_a` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)

```lean
theorem constComposite_a (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.a = constLens d.a := by
  unfold constComposite
  rw [@universalMorphism_a α d]
```

## `constComposite_b` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)

```lean
theorem constComposite_b (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.b = constLens d.b := by
  unfold constComposite
  rw [@universalMorphism_b α d]
```

## `constComposite_slash` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)

```lean
theorem constComposite_slash (α : Type) [d : HasDistinguishing α]
    (x y : Raw) (h : x ≠ y) :
    constComposite α (Raw.slash x y h) =
      lensCombineGeneric d.combine (constComposite α x) (constComposite α y) := by
  unfold constComposite
  rw [@universalMorphism_slash α d x y h]
  exact (lensCombineGeneric_const d.combine _ _).symm
```

## `boolAndLens_view_const` (E213/Hypervisor/Lens/Instances/Bool.lean)

```lean
theorem boolAndLens_view_const (r : Raw) : boolAndLens.view r = true := by
  show Raw.fold true true (· && ·) r = true
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      rw [Raw.fold_slash _ _ _ (fun u v => by cases u <;> cases v <;> rfl) x y h,
          ihx, ihy]
      decide
```

## `boolOrLens_view_const` (E213/Hypervisor/Lens/Instances/Bool.lean)

```lean
theorem boolOrLens_view_const (r : Raw) : boolOrLens.view r = true := by
  show Raw.fold true true (· || ·) r = true
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      rw [Raw.fold_slash _ _ _ (fun u v => by cases u <;> cases v <;> rfl) x y h,
          ihx, ihy]
      decide
```

## `eventually_class_unique` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem eventually_class_unique {α : Type} (L : Lens α) (xs : Nat → Raw)
    (c c' : α) (h : EventuallyClass L xs c) (h' : EventuallyClass L xs c') :
    c = c' := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨N', hN'⟩ := h'
  let M := max N N'
  have hMN : M ≥ N := Nat.le_max_left N N'
  have hMN' : M ≥ N' := Nat.le_max_right N N'
  rw [← hN M hMN, hN' M hMN']
```

## `parityXor_fst_eq_parity` (E213/Hypervisor/Lens/Instances/CompoundBool.lean)

```lean
theorem parityXor_fst_eq_parity (r : Raw) :
    (parityXorLens.view r).1 = parityLens.view r := by
  show (Raw.fold (true, true) (true, false)
         (fun p q => (xor p.1 q.1, xor p.2 q.2)) r).1
       = Raw.fold true true xor r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hsym_pair :
          ∀ (u v : Bool × Bool),
            (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) u v
          = (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) v u := by
        intro u v
        simp [Bool.xor_comm]
      have hsym_xor : ∀ u v : Bool
... [truncated]
```

## `parityXor_snd_eq_boolXor` (E213/Hypervisor/Lens/Instances/CompoundBool.lean)

```lean
theorem parityXor_snd_eq_boolXor (r : Raw) :
    (parityXorLens.view r).2 = boolXorLens.view r := by
  show (Raw.fold (true, true) (true, false)
         (fun p q => (xor p.1 q.1, xor p.2 q.2)) r).2
       = Raw.fold true false xor r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hsym_pair :
          ∀ (u v : Bool × Bool),
            (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) u v
          = (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) v u := by
        intro u v
        simp [Bool.xor_comm]
      have hsym_xor : ∀ u v : B
... [truncated]
```

## `parityXor_ab` (E213/Hypervisor/Lens/Instances/CompoundBool.lean)

```lean
theorem parityXor_ab : parityXorLens.view ab = (false, true) := by
  show Raw.fold (true, true) (true, false)
         (fun p q => (xor p.1 q.1, xor p.2 q.2))
         (Raw.slash Raw.a Raw.b (by decide)) = (false, true)
  have hsym_pair :
      ∀ (u v : Bool × Bool),
        (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) u v
      = (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) v u := by
    intro u v
    simp [Bool.xor_comm]
  rw [Raw.fold_slash _ _ _ hsym_pair Raw.a Raw.b (by decide)]
  rfl

/-- **Image cardinality ≥ 3**: three distinct Raw terms give
    three distinct Bool ×
... [truncated]
```

## `f9Lens_view_ab` (E213/Hypervisor/Lens/Instances/F9.lean)

```lean
theorem f9Lens_view_ab :
    f9Lens.view (Raw.slash Raw.a Raw.b (by decide)) = F9.i := by
  show Raw.fold F9.one F9.i F9.mul (Raw.slash Raw.a Raw.b _) = F9.i
  rw [Raw.fold_slash F9.one F9.i F9.mul F9.mul_comm Raw.a Raw.b (by decide)]
  rfl
```

## `universalMorphism_pair_commute` (E213/Hypervisor/Lens/Instances/Pair.lean)

```lean
theorem universalMorphism_pair_commute (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    @universalMorphism (α × β) (pairHasDistinguishing α β) r
      = (universalMorphism α r, universalMorphism β r) := by
  induction r using Raw.rec with
  | a =>
      have h_pair : @universalMorphism (α × β) (pairHasDistinguishing α β) Raw.a
                    = (d_α.a, d_β.a) :=
        @universalMorphism_a (α × β) (pairHasDistinguishing α β)
      have h_α : universalMorphism α Raw.a = d_α.a := universalMorphism_a α
      have h_β : universalMorphism β Raw.a = d_β.a
... [truncated]
```

## `universalMorphism_first` (E213/Hypervisor/Lens/Instances/Pair.lean)

```lean
theorem universalMorphism_first (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    Prod.fst (@universalMorphism (α × β) (pairHasDistinguishing α β) r)
      = universalMorphism α r := by
  rw [universalMorphism_pair_commute]
```

## `universalMorphism_second` (E213/Hypervisor/Lens/Instances/Pair.lean)

```lean
theorem universalMorphism_second (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    Prod.snd (@universalMorphism (α × β) (pairHasDistinguishing α β) r)
      = universalMorphism β r := by
  rw [universalMorphism_pair_commute]
```

## `parityLens_sample_even_view` (E213/Hypervisor/Lens/Instances/Parity.lean)

```lean
theorem parityLens_sample_even_view :
    parityLens.view parityLens_sample_even = false := by
  show Raw.fold true true xor (Raw.slash Raw.a Raw.b _) = false
  rw [Raw.fold_slash true true xor xor_comm_bool Raw.a Raw.b (by decide)]
  rfl

/-- **R4 fails.**  Swap-blindness forces any matching `conj`
    to fix every image point; with both `true` and `false`
    reachable, that forces `conj = id`, contradicting the
    `conj ≠ id` clause of R4. -/
```

## `pathLens_view_ba_via_comm` (E213/Hypervisor/Lens/Instances/Path.lean)

```lean
theorem pathLens_view_ba_via_comm :
    pathLens.view (Raw.slash Raw.b Raw.a (by decide))
      = [false, true] := by
  rw [Raw.slash_comm]; rfl
```

## `aPrism_a` (E213/Hypervisor/Lens/Instances/Prism.lean)

```lean
theorem aPrism_a : aPrism.preview Raw.a = some () := by
  unfold aPrism caseElement
  show (if (Raw.a : Raw) = Raw.a then some () else none) = some ()
  rw [if_pos rfl]
```

## `aPrism_b` (E213/Hypervisor/Lens/Instances/Prism.lean)

```lean
theorem aPrism_b : aPrism.preview Raw.b = none := by
  unfold aPrism caseElement
  show (if (Raw.b : Raw) = Raw.a then some () else none) = none
  rw [if_neg (by decide)]
```

## `bPrism_a` (E213/Hypervisor/Lens/Instances/Prism.lean)

```lean
theorem bPrism_a : bPrism.preview Raw.a = none := by
  unfold bPrism caseElement
  show (if (Raw.a : Raw) = Raw.b then some () else none) = none
  rw [if_neg (by decide)]
```

## `bPrism_b` (E213/Hypervisor/Lens/Instances/Prism.lean)

```lean
theorem bPrism_b : bPrism.preview Raw.b = some () := by
  unfold bPrism caseElement
  show (if (Raw.b : Raw) = Raw.b then some () else none) = some ()
  rw [if_pos rfl]
```

## `nat_image_via_slash_ab` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem nat_image_via_slash_ab :
    universalMorphism Nat (Raw.slash Raw.a Raw.b (by decide)) = 1 := by
  rw [universalMorphism_slash Nat Raw.a Raw.b (by decide)]
  rw [universalMorphism_a Nat, universalMorphism_b Nat]
  rfl
```

## `subtypeCombine_comm` (E213/Hypervisor/Lens/Instances/SubtypeClosed.lean)

```lean
theorem subtypeCombine_comm (P : Raw → Prop) [SlashClosed P]
    (h_a : P Raw.a) (x y : {r : Raw // P r}) :
    subtypeCombine P h_a x y = subtypeCombine P h_a y x := by
  unfold subtypeCombine
  by_cases h : x.val = y.val
  · have hsym : y.val = x.val := h.symm
    rw [dif_pos h, dif_pos hsym]
  · have hsym : y.val ≠ x.val := fun e => h e.symm
    rw [dif_neg h, dif_neg hsym]
    apply Subtype.ext
    exact Raw.slash_comm _ _ h
```

## `constLens_view` (E213/Hypervisor/Lens/Lattice/Lattice.lean)

```lean
theorem constLens_view {α : Type} (e : α) (r : Raw) :
    (constLens e).view r = e := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : (constLens e).view (Raw.slash x y h)
                   = (constLens e).combine
                       ((constLens e).view x) ((constLens e).view y) :=
        Raw.fold_slash _ _ _ (by intro _ _; rfl) x y h
      rw [hfs]; rfl
```

## `tierLens_view_eq_tier` (E213/Hypervisor/Lens/Leaves/DepthJoin.lean)

```lean
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
      show (if tier x = 0 ∧ tier y = 0 t
... [truncated]
```

## `universalMorphism_commute` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem universalMorphism_commute (r : Raw) :
    @universalMorphism Prop propAsDistinguishingAnd r
      = boolToProp (universalMorphism Bool r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingAnd Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishingAnd
      have h2 : universalMorphism Bool Raw.a = true :=
        universalMorphism_a Bool
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistinguishingAnd Raw.b = False :=
        @universalMorphism_b Prop propAsDistinguishingA
... [truncated]
```

## `universalMorphism_commute_xor` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem universalMorphism_commute_xor (r : Raw) :
    @universalMorphism Prop propAsDistinguishing r
      = boolToProp (@universalMorphism Bool boolXorHasDistinguishing r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishing Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishing
      have h2 : @universalMorphism Bool boolXorHasDistinguishing Raw.a = true :=
        @universalMorphism_a Bool boolXorHasDistinguishing
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistinguishing Ra
... [truncated]
```

## `universalMorphism_commute_or` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem universalMorphism_commute_or (r : Raw) :
    @universalMorphism Prop propAsDistinguishingOr r
      = boolToProp (@universalMorphism Bool boolOrHasDistinguishing r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingOr Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishingOr
      have h2 : @universalMorphism Bool boolOrHasDistinguishing Raw.a = true :=
        @universalMorphism_a Bool boolOrHasDistinguishing
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistinguishingO
... [truncated]
```

## `universalMorphism_commute_iff` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem universalMorphism_commute_iff (r : Raw) :
    @universalMorphism Prop propAsDistinguishingIff r
      = boolToProp (@universalMorphism Bool boolIffHasDistinguishing r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingIff Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishingIff
      have h2 : @universalMorphism Bool boolIffHasDistinguishing Raw.a = true :=
        @universalMorphism_a Bool boolIffHasDistinguishing
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistingu
... [truncated]
```

## `depth_equal` (E213/Hypervisor/Lens/Properties/ProdBelowId.lean)

```lean
theorem depth_equal : Lens.depth.view rA = Lens.depth.view rB := by decide

private theorem leaves_sym : ∀ u v : Nat, u + v = v + u := Nat.add_comm

private theorem depth_sym :
    ∀ u v : Nat, 1 + max u v = 1 + max v u := by
  intro u v; rw [Nat.max_comm]

/-- prod of (leaves, depth) equates rA and rB. -/
```

## `prod_equates` (E213/Hypervisor/Lens/Properties/ProdBelowId.lean)

```lean
theorem prod_equates :
    (prodLens Lens.leaves Lens.depth).view rA
      = (prodLens Lens.leaves Lens.depth).view rB := by
  rw [prodLens_view _ _ leaves_sym depth_sym,
      prodLens_view _ _ leaves_sym depth_sym,
      leaves_equal, depth_equal]

/-- **idLens distinguishes them** (they are unequal Raw). -/
```

## `mod_mod` (E213/Math/AddMod213.lean)

```lean
theorem mod_mod (a n : Nat) : a % n % n = a % n := by
  by_cases h : 0 < n
  · exact Nat.mod_eq_of_lt (Nat.mod_lt _ h)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst hn0
    rw [Nat.mod_zero, Nat.mod_zero]

/-- `0 % a = 0`.  ∅-axiom. -/
```

## `add_mod` (E213/Math/AddMod213.lean)

```lean
theorem add_mod {n : Nat} (hn : 0 < n) (a b : Nat) :
    (a + b) % n = (a % n + b % n) % n := by
  rw [add_mod_left hn a b]
  rw [Nat.add_comm (a % n) b, add_mod_left hn b (a % n), Nat.add_comm]

/-- `b * (a / b) + a % b = a` for all `a b`.  ∅-axiom replacement
    for `Nat.div_add_mod` (which leaks propext). -/
```

## `max_comm` (E213/Math/AddMod213.lean)

```lean
theorem max_comm (a b : Nat) : Nat.max a b = Nat.max b a := by
  rcases Nat.le_total a b with hab | hba
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hab]
    by_cases h : b ≤ a
    · rw [if_pos h]; exact Nat.le_antisymm h hab
    · rw [if_neg h]
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hba]
    by_cases h : a ≤ b
    · rw [if_pos h]; exact Nat.le_antisymm hba h
    · rw [if_neg h]
```

## `rational_seq_orderProj_const` (E213/Math/Cauchy/Archimedean.lean)

```lean
theorem rational_seq_orderProj_const (p q m k : Nat) (n : Nat) (hn : n ≥ 1) :
    orderProj m k (p * n, q * n) = decide (p * k ≤ q * m) := by
  unfold orderProj
  show decide (p * n * k ≤ q * n * m) = decide (p * k ≤ q * m)
  have hrw1 : p * n * k = (p * k) * n := by
    rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm n k,
        ← E213.Tactic.Nat213.mul_assoc]
  have hrw2 : q * n * m = (q * m) * n := by
    rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm n m,
        ← E213.Tactic.Nat213.mul_assoc]
  rw [hrw1, hrw2]
  by_cases hpq : p * k ≤ q * m
  · have h : (p * k) * n ≤ (q * m) * n := Nat.m
... [truncated]
```
