# Cluster `equality_rfl` — 519 decls (sample limited to 50)

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

## `Ordering_swap_swap` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem Ordering_swap_swap (o : Ordering) : o.swap.swap = o := by
  cases o <;> rfl

/-- cmpRev also satisfies CmpProps (involutive). -/
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

## `transport_a` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem transport_a (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    transport cmp1 cmp2 h1 h2 (RawBy.a cmp1) = RawBy.a cmp2 := rfl

/-- transport of RawBy.b. -/
```

## `Raw` (E213/Firmware/Raw/Fold.lean)

```lean
def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl
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

## `Raw` (E213/Firmware/RawLevels.lean)

```lean
def Raw.level1_set : List Raw :=
  [Raw.a, Raw.b, Raw.slash Raw.a Raw.b (by decide)]

/-- Level-2 additions: the Raw terms `a/(a/b)`, `b/(a/b)`. -/
```

## `eq_implies_pointwiseEq` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)

```lean
theorem eq_implies_pointwiseEq {α β : Type} {f g : α → β} (h : f = g) :
    pointwiseEq f g := fun x => h ▸ rfl

/-- The non-trivial direction (pointwise eq → Eq) IS funext.
    Stated here as a *type-level claim*; the actual axiomatic
    inhabitant lives in `AxiomLenses/Bridges/Funext.lean`. -/
```

## `lensXor_comm` (E213/Hypervisor/Lens/Compose/OnLens.lean)

```lean
theorem lensXor_comm (L M : Lens Bool) : lensXor L M = lensXor M L := by
  unfold lensXor
  -- Structural equality on Lens record.
  congr 1
  · cases L.base_a <;> cases M.base_a <;> rfl
  · cases L.base_b <;> cases M.base_b <;> rfl
  · funext x y
    cases L.combine x y <;> cases M.combine x y <;> rfl
```

## `boolToConstLens_true` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl
```

## `boolToConstLens_false` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem boolToConstLens_false : boolToConstLens false = constFalseLens := rfl
```

## `lensXor_TT` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem lensXor_TT : lensXor constTrueLens constTrueLens = constFalseLens := by
  unfold lensXor constTrueLens constFalseLens; rfl
```

## `lensXor_TF` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem lensXor_TF : lensXor constTrueLens constFalseLens = constTrueLens := by
  unfold lensXor constTrueLens; rfl
```

## `lensXor_FT` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem lensXor_FT : lensXor constFalseLens constTrueLens = constTrueLens := by
  unfold lensXor constTrueLens constFalseLens; rfl
```

## `lensCombineGeneric_const` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)

```lean
theorem lensCombineGeneric_const {α : Type} (c : α → α → α) (a b : α) :
    lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b) := by
  unfold lensCombineGeneric constLens; rfl
```

## `Lens` (E213/Hypervisor/Lens/Initiality.lean)

```lean
theorem Lens.view_unique {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (f : Raw → α)
    (ha : f Raw.a = L.base_a)
    (hb : f Raw.b = L.base_b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = L.combine (f x) (f y)) :
    ∀ r : Raw, f r = L.view r := by
  intro r
  induction r using Raw.rec with
  | a => rw [ha]; rfl
  | b => rw [hb]; rfl
  | slash x y h ihx ihy =>
      rw [hslash x y h, ihx, ihy]
      -- Goal: L.combine (L.view x) (L.view y) = L.view (Raw.slash x y h).
      -- Resolved by Raw.fold_slash.
      symm
      show
... [truncated]
```

## `limitLens_tail_collapse` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem limitLens_tail_collapse (xs : Nat → Raw) (N : Nat)
    (m k : Nat) (hm : m ≥ N) (hk : k ≥ N) :
    (limitLens xs N).view (xs m) = (limitLens xs N).view (xs k) :=
  (limitLens_kernel xs N (xs m) (xs k)).mpr (TailCong.tail_eq m k hm hk)

/-- TailCong ⊆ N.equiv (helper for universal property). -/
private theorem tailCong_implies_equiv {α : Type} (N : Lens α)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (xs : Nat → Raw) (M : Nat)
    (hCollapse : ∀ m k, m ≥ M → k ≥ M → N.equiv (xs m) (xs k))
    (r r' : Raw) (h : TailCong xs M r r') :
    N.equiv r r' := by
  induction h with
  |
... [truncated]
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

## `f9Lens_view_a` (E213/Hypervisor/Lens/Instances/F9.lean)

```lean
theorem f9Lens_view_a : f9Lens.view Raw.a = F9.one := rfl

/-- Concrete view check: view b = i. -/
```

## `f9Lens_view_b` (E213/Hypervisor/Lens/Instances/F9.lean)

```lean
theorem f9Lens_view_b : f9Lens.view Raw.b = F9.i := rfl

/-- F9 multiplication is commutative — structural proof via
    F3.mul_comm and F3.add_comm.  No ∀-Decidable needed. -/
```

## `maxLens_view_ab` (E213/Hypervisor/Lens/Instances/Max.lean)

```lean
theorem maxLens_view_ab :
    maxLens.view (Raw.slash Raw.a Raw.b (by decide)) = 1 := rfl

/-- `slash a b` is swap-invariant at the Raw level.  Tree.swap
    sends `slash a b` to `slash (swap a) (swap b) = slash b a`
    which re-canonicalises back to `slash a b`. -/
```

## `slash_ab_swap_fixed` (E213/Hypervisor/Lens/Instances/Max.lean)

```lean
theorem slash_ab_swap_fixed :
    Raw.swap (Raw.slash Raw.a Raw.b (by decide))
      = Raw.slash Raw.a Raw.b (by decide) := by
  apply Subtype.ext; rfl
```

## `negSqLens_sq` (E213/Hypervisor/Lens/Instances/NegSq.lean)

```lean
theorem negSqLens_sq (v : Bool) : sq negSqLens v = !v := by
  cases v <;> rfl

/-- negSqLens is not Idempotent (sq v = !v ≠ v). -/
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

## `pair_forget_first_a` (E213/Hypervisor/Lens/Instances/Pair.lean)

```lean
theorem pair_forget_first_a (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.fst (pairHasDistinguishing α β).a = d_α.a := rfl
```

## `pair_forget_first_b` (E213/Hypervisor/Lens/Instances/Pair.lean)

```lean
theorem pair_forget_first_b (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.fst (pairHasDistinguishing α β).b = d_α.b := rfl
```

## `pair_forget_first_combine` (E213/Hypervisor/Lens/Instances/Pair.lean)

```lean
theorem pair_forget_first_combine (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (p q : α × β) :
    Prod.fst ((pairHasDistinguishing α β).combine p q)
      = d_α.combine (Prod.fst p) (Prod.fst q) := rfl
```

## `pair_forget_second_a` (E213/Hypervisor/Lens/Instances/Pair.lean)

```lean
theorem pair_forget_second_a (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.snd (pairHasDistinguishing α β).a = d_β.a := rfl
```

## `parityLens_swap_invariant` (E213/Hypervisor/Lens/Instances/Parity.lean)

```lean
theorem parityLens_swap_invariant (r : Raw) :
    parityLens.view (Raw.swap r) = parityLens.view r := by
  have h := Raw.fold_swap_hom (true : Bool) true xor id
    (rfl) (rfl)
    (fun _ _ => rfl)
    xor_comm_bool
    r
  exact h
```

## `pathLens_view_ab` (E213/Hypervisor/Lens/Instances/Path.lean)

```lean
theorem pathLens_view_ab :
    pathLens.view (Raw.slash Raw.a Raw.b (by decide))
      = [false, true] := rfl
```

## `pathLens_view_ba_via_comm` (E213/Hypervisor/Lens/Instances/Path.lean)

```lean
theorem pathLens_view_ba_via_comm :
    pathLens.view (Raw.slash Raw.b Raw.a (by decide))
      = [false, true] := by
  rw [Raw.slash_comm]; rfl
```

## `pathLens_view_a_slash_ab` (E213/Hypervisor/Lens/Instances/Path.lean)

```lean
theorem pathLens_view_a_slash_ab :
    pathLens.view (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide))
      (by decide))
      = [false, false, true] := rfl
```

## `pathLens_view_b_slash_ab` (E213/Hypervisor/Lens/Instances/Path.lean)

```lean
theorem pathLens_view_b_slash_ab :
    pathLens.view (Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide))
      (by decide))
      = [true, false, true] := rfl

-- ═══ R2 (combine commutativity) FAILS ═══

/-- **`pathLens.combine` is NOT commutative.**  Concrete witness:
    `append [false] [true] = [false, true]` but
    `append [true] [false] = [true, false]`. -/
```

## `aPrism_a` (E213/Hypervisor/Lens/Instances/Prism.lean)

```lean
theorem aPrism_a : aPrism.preview Raw.a = some () := by
  unfold aPrism caseElement
  show (if (Raw.a : Raw) = Raw.a then some () else none) = some ()
  rw [if_pos rfl]
```

## `bPrism_b` (E213/Hypervisor/Lens/Instances/Prism.lean)

```lean
theorem bPrism_b : bPrism.preview Raw.b = some () := by
  unfold bPrism caseElement
  show (if (Raw.b : Raw) = Raw.b then some () else none) = some ()
  rw [if_pos rfl]
```

## `leafLens_equates_a_b` (E213/Hypervisor/Lens/Instances/RawAChar.lean)

```lean
theorem leafLens_equates_a_b :
    leafLens.view Raw.a = leafLens.view Raw.b := rfl
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

## `tier_invariant` (E213/Hypervisor/Lens/Leaves/DepthJoin.lean)

```lean
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

## `boolToProp_true` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem boolToProp_true : boolToProp true = True := by
  unfold boolToProp
  apply propext
  exact ⟨fun _ => trivial, fun _ => rfl⟩
```

## `comp_assoc` (E213/Hypervisor/Lens/Morphism/Dist.lean)

```lean
theorem comp_assoc {α β γ δ : Type}
    [HasDistinguishing α] [HasDistinguishing β]
    [HasDistinguishing γ] [HasDistinguishing δ]
    (f : DistMorphism α β) (g : DistMorphism β γ) (h : DistMorphism γ δ) :
    comp (comp f g) h = comp f (comp g h) := rfl

/-- Identity is left-neutral for composition. -/
```

## `id_comp` (E213/Hypervisor/Lens/Morphism/Dist.lean)

```lean
theorem id_comp {α β : Type} [HasDistinguishing α] [HasDistinguishing β]
    (f : DistMorphism α β) :
    comp (id α) f = f := rfl

/-- Identity is right-neutral for composition. -/
```

## `comp_id` (E213/Hypervisor/Lens/Morphism/Dist.lean)

```lean
theorem comp_id {α β : Type} [HasDistinguishing α] [HasDistinguishing β]
    (f : DistMorphism α β) :
    comp f (id β) = f := rfl
```

## `isLeafLens_a` (E213/Hypervisor/Lens/Properties/IsLeaf.lean)

```lean
theorem isLeafLens_a : isLeafLens.view Raw.a = true := rfl
```
