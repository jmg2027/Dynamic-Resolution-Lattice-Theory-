# Cluster implication_thm — 483 decls (sample 50)

## \`block_constant_implies_aut_invariant\` (E213/App/Simplex.lean)

```lean
theorem block_constant_implies_aut_invariant {α : Type}
    (W : Fin 5 → Fin 5 → α) (h : BlockConstant W) : AutInvariant W := by
  obtain ⟨f, hf⟩ := h
  intro σ hσ hinj i j
  rw [hf (σ i) (σ j), hf i j]
  -- classify (σ i) (σ j) = classify i j : partition is preserved and
  -- i = j ↔ σ i = σ j (by injectivity).
  have hi : isA (σ i) = isA i := hσ i
  have hj : isA (σ j) = isA j := hσ j
  have heq : (σ i = σ j) ↔ (i = j) :=
    ⟨fun h => hinj i j h, fun h => h ▸ rfl⟩
  simp [classify, hi, hj, heq]
```

## \`reachable_isBase\` (E213/Firmware/Atomicity/ArityForcingGeneral.lean)

```lean
theorem reachable_isBase {N k : Nat} (h : N < k) :
    ∀ {x : RawNk N k}, ReachableNk x → isBase x = true := by
  intro x hr
  induction hr with
  | base i => rfl
  | @step f _ hne ih =>
      exfalso
      let g : Fin k → Fin N := fun i => getBase (f i) (ih i)
      have hgeq : ∀ i, f i = .object (g i) :=
        fun i => getBase_eq (f i) (ih i)
      have g_inj : ∀ i j : Fin k, i ≠ j → g i ≠ g j := by
        intro i j hij heq
        apply hne i j hij
        rw [hgeq i, hgeq j, heq]
      exact E213.Math.Pigeonhole.no_inj_lt h g g_inj

/-- **Main vacuousness theorem.** If `N < k`, every Re
... [truncated]
```

## \`no_reachable_rel\` (E213/Firmware/Atomicity/ArityForcingGeneral.lean)

```lean
theorem no_reachable_rel {N k : Nat} (h : N < k)
    (f : Fin k → RawNk N k) : ¬ ReachableNk (RawNk.rel f) := by
  intro hr
  have hb : isBase (RawNk.rel f) = true := reachable_isBase h hr
  cases hb

-- Summary: `(arity k, base Fin N)` is non-vacuous iff `N ≥ k`.
-- Combined with arity ≥ 2 (non-degenerate) and N minimal,
-- `(k = 2, N = 2)` is the unique minimal non-degenerate, non-vacuous
-- choice.
```

## \`canonical_partition\` (E213/Firmware/Atomicity/Five.lean)

```lean
theorem canonical_partition :
    ∀ a b, Decomp 5 a b ∧ IsAlive a b → a = 1 ∧ b = 1 := by
  intro a b ⟨hdec, _⟩
  exact solve_2a_3b_eq_5 a b hdec.symm
```

## \`Tree\` (E213/Firmware/Raw/Cmp.lean)

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

## \`Bool\` (E213/Firmware/Raw/Cmp.lean)

```lean
theorem Bool.and_eq_true_to_pair : ∀ {a b : Bool},
    (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => by cases h
  | true, false, h => by cases h
```

## \`cmpRev_props\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem cmpRev_props (cmp : Tree → Tree → Ordering) (h : CmpProps cmp) :
    CmpProps (cmpRev cmp) where
  eq_iff := by
    intro x y
    unfold cmpRev
    constructor
    · intro hsw
      have : cmp x y = .eq := by
        cases hcmp : cmp x y with
        | eq => rfl
        | lt => rw [hcmp] at hsw; cases hsw
        | gt => rw [hcmp] at hsw; cases hsw
      exact (h.eq_iff x y).mp this
    · intro hxy
      rw [hxy]
      have : cmp y y = .eq := (h.eq_iff y y).mpr rfl
      rw [this]; rfl
  swap := by
    intro x y
    unfold cmpRev
    rw [h.swap x y, Ordering_swap_swap]
```

## \`slashTree_comm\` (E213/Firmware/Raw/CmpIndependence.lean)

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

## \`RawBy_slash_val\` (E213/Firmware/Raw/CmpIndependence.lean)

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

## \`RawBy\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
def RawBy (cmp : Tree → Tree → Ordering) : Type :=
  { t : Tree // canonicalBy cmp t = true }

/-- When using the original Tree.cmp, canonicalBy = Tree.canonical. -/
```

## \`Raw\` (E213/Firmware/Raw/Fold.lean)

```lean
def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl
```

## \`Tree\` (E213/Firmware/Raw/Hom.lean)

```lean
theorem Tree.fold_swap_hom {α : Type}
    (ba bb : α) (c : α → α → α) (conj : α → α)
    (h_ba : conj ba = bb) (h_bb : conj bb = ba)
    (h_dist : ∀ u v, conj (c u v) = c (conj u) (conj v))
    (h_comm : ∀ u v, c u v = c v u) :
    ∀ t : Tree, t.canonical = true →
    Tree.fold ba bb c (Tree.swap t) = conj (Tree.fold ba bb c t) := by
  intro t h
  induction t with
  | a => exact h_ba.symm
  | b => exact h_bb.symm
  | slash x y ihx ihy =>
      have hc := h
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hlt := Tree.canonical_slash_lt h
     
... [truncated]
```

## \`Raw\` (E213/Firmware/Raw/Hom.lean)

```lean
theorem Raw.fold_swap_hom {α : Type}
    (ba bb : α) (c : α → α → α) (conj : α → α)
    (h_ba : conj ba = bb) (h_bb : conj bb = ba)
    (h_dist : ∀ u v, conj (c u v) = c (conj u) (conj v))
    (h_comm : ∀ u v, c u v = c v u) (r : Raw) :
    Raw.fold ba bb c (Raw.swap r) = conj (Raw.fold ba bb c r) :=
  Tree.fold_swap_hom ba bb c conj h_ba h_bb h_dist h_comm r.val r.property
```

## \`Tree\` (E213/Firmware/Raw/Levels.lean)

```lean
theorem Tree.swap_depth :
    ∀ t : Tree, t.canonical = true → (Tree.swap t).depth = t.depth := by
  intro t h
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      have hc := h
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp
      · simp only [Tree.depth, ihx', ihy']
      · simp only [Tree.depth, ihx', ihy', Nat.max_comm]
      · exact (Tree.swap_eq_unreach hx hy hlt hcmp).elim
```

## \`Tree\` (E213/Firmware/Raw/Signed.lean)

```lean
theorem Tree.fold_signed_swap :
    ∀ t : Tree, t.canonical = true →
    Tree.fold (1 : Int) (-1) (· + ·) (Tree.swap t)
      = - Tree.fold (1 : Int) (-1) (· + ·) t := by
  intro t h
  induction t with
  | a => decide
  | b => decide
  | slash x y ihx ihy =>
      have hc := h
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp_inner
      · show Tree.fold _ _ _ (Tree.swap x) + Tree.fold _ _ _ (Tree.swap 
... [truncated]
```

## \`Tree\` (E213/Firmware/Raw/Swap.lean)

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

## \`funextLens_inhabited\` (E213/Hypervisor/Lens/AxiomLenses/Bridges/Funext.lean)

```lean
theorem funextLens_inhabited {α β : Type} (f g : α → β) :
    funextLens f g := funext
```

## \`pointwiseEq_refl\` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)

```lean
theorem pointwiseEq_refl {α β : Type} (f : α → β) : pointwiseEq f f :=
  fun _ => rfl
```

## \`pointwiseEq_symm\` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)

```lean
theorem pointwiseEq_symm {α β : Type} {f g : α → β}
    (h : pointwiseEq f g) : pointwiseEq g f :=
  fun x => (h x).symm
```

## \`pointwiseEq_trans\` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)

```lean
theorem pointwiseEq_trans {α β : Type} {f g h : α → β}
    (hfg : pointwiseEq f g) (hgh : pointwiseEq g h) : pointwiseEq f h :=
  fun x => (hfg x).trans (hgh x)

/-- The trivial direction (Eq → pointwise eq) is constructive. -/
```

## \`eq_implies_pointwiseEq\` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)

```lean
theorem eq_implies_pointwiseEq {α β : Type} {f g : α → β} (h : f = g) :
    pointwiseEq f g := fun x => h ▸ rfl

/-- The non-trivial direction (pointwise eq → Eq) IS funext.
    Stated here as a *type-level claim*; the actual axiomatic
    inhabitant lives in `AxiomLenses/Bridges/Funext.lean`. -/
```

## \`swap_invariant_R4_fixes_image\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
theorem swap_invariant_R4_fixes_image
    {α : Type} {L : Hypervisor.Lens α} {conj : α → α}
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r)
    (hmatch : SwapMatching L conj)
    (r : Raw) : conj (L.view r) = L.view r := by
  have h1 : L.view (Raw.swap r) = conj (L.view r) := hmatch.2.2 r
  have h2 : L.view (Raw.swap r) = L.view r := hinv r
  rw [h2] at h1
  exact h1.symm
```

## \`R4_conj_agrees_on_image\` (E213/Hypervisor/Lens/Characterisation/Core.lean)

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

## \`R4_conj_unique_of_surjective\` (E213/Hypervisor/Lens/Characterisation/Core.lean)

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

## \`R3_view_nonVanishing\` (E213/Hypervisor/Lens/Characterisation/Core.lean)

```lean
theorem R3_view_nonVanishing
    {α : Type} [Zero α] (L : Hypervisor.Lens α)
    (hba : L.base_a ≠ 0) (hbb : L.base_b ≠ 0)
    (hcomm : ∀ u v : α, L.combine u v = L.combine v u)
    (hnz : ∀ u v : α, L.combine u v = 0 → u = 0 ∨ v = 0)
    (r : Raw) : L.view r ≠ 0 := by
  induction r using Raw.rec with
  | a => show L.base_a ≠ 0; exact hba
  | b => show L.base_b ≠ 0; exact hbb
  | slash x y h ihx ihy =>
      show L.view (Raw.slash x y h) ≠ 0
      have hstep : L.view (Raw.slash x y h)
                     = L.combine (L.view x) (L.view y) := by
        show Raw.fold L.base_a L.base_b L.combine
... [truncated]
```

## \`refines_of_factor\` (E213/Hypervisor/Lens/Compose/Factoring.lean)

```lean
theorem refines_of_factor {α β : Type} (L : Lens α) (M : Lens β)
    (g : α → β) (hfactor : ∀ r : Raw, M.view r = g (L.view r)) :
    L.refines M := by
  intro x y hxy
  have hxy' : L.view x = L.view y := hxy
  show M.view x = M.view y
  rw [hfactor x, hfactor y, hxy']
```

## \`image_minimum_property\` (E213/Hypervisor/Lens/Compose/ImageMinimum.lean)

```lean
theorem image_minimum_property (α) [d : HasDistinguishing α]
    (S : α → Prop)
    (hSa : S d.a) (hSb : S d.b)
    (hSclosed : ∀ x y, S x → S y → S (d.combine x y)) :
    ∀ r : Raw, S (universalMorphism α r)
```

## Significance

Exact algebraic content of the framework's reach:
- For all S : α → Prop with `d.a, d.b ∈ S` and `S` closed under
  combine, image of universalMorphism ⊆ S.
- That is, the image is the *minimum* distinguishing-closed subset of α.
- → The framework's reach is the strict minimum of
  "distinguishable-closed sub-instances".

## Component of the complete semantic 213 pro
... [truncated]
```

## \`view_factors_through_morphism\` (E213/Hypervisor/Lens/Compose/Morphism.lean)

```lean
theorem view_factors_through_morphism {α β : Type}
    (L : Lens α) (M : Lens β) (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) :
    ∀ r : Raw, M.view r = h (L.view r) := by
  obtain ⟨hba, hbb, hcomb⟩ := hmor
  intro r
  induction r using Raw.rec with
  | a => show M.base_a = h L.base_a; exact hba.symm
  | b => show M.base_b = h L.base_b; exact hbb.symm
  | slash x y hxy ihx ihy =>
      have hfsM : M.view (Raw.slash x y hxy)
                    = M.combine (M.view x) (M.view y) :=
   
... [truncated]
```

## \`refines_of_morphism\` (E213/Hypervisor/Lens/Compose/Morphism.lean)

```lean
theorem refines_of_morphism {α β : Type} (L : Lens α) (M : Lens β)
    (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) : L.refines M := by
  intro x y hxy
  have hx : M.view x = h (L.view x) :=
    view_factors_through_morphism L M h hLsym hMsym hmor x
  have hy : M.view y = h (L.view y) :=
    view_factors_through_morphism L M h hLsym hMsym hmor y
  have hxy' : L.view x = L.view y := hxy
  show M.view x = M.view y
  rw [hx, hy, hxy']
```

## \`lensCombineGeneric_comm\` (E213/Hypervisor/Lens/Compose/OnLens.lean)

```lean
theorem lensCombineGeneric_comm {α : Type} (c : α → α → α)
    (hsym : ∀ u v, c u v = c v u) (L M : Lens α) :
    lensCombineGeneric c L M = lensCombineGeneric c M L := by
  unfold lensCombineGeneric
  congr 1
  · exact hsym _ _
  · exact hsym _ _
  · funext x y; exact hsym _ _
```

## \`lensCombineGeneric_const\` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)

```lean
theorem lensCombineGeneric_const {α : Type} (c : α → α → α) (a b : α) :
    lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b) := by
  unfold lensCombineGeneric constLens; rfl
```

## \`Lens\` (E213/Hypervisor/Lens/Foundations/Initiality.lean)

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

## \`bool_not_ne_id\` (E213/Hypervisor/Lens/Instances/Bool.lean)

```lean
theorem bool_not_ne_id : (!·) ≠ (id : Bool → Bool) := by
  intro h
  have : (!true) = id true := congrFun h true
  exact absurd this (by decide)

/-- **R4 fails for `boolXorLens`.**  The homomorphism clause
    (Lens.combine distributing over `not`) is what fails:
    explicitly, `!(true xor false) = false` but
    `(!true) xor (!false) = false xor true = true`. -/
```

## \`boundedEq_refl\` (E213/Hypervisor/Lens/Instances/BoundedContext.lean)

```lean
theorem boundedEq_refl (N : Nat) {α : Type} (f : Nat → α) :
    boundedEq N f f := fun _ => rfl
```

## \`boundedEq_symm\` (E213/Hypervisor/Lens/Instances/BoundedContext.lean)

```lean
theorem boundedEq_symm {N : Nat} {α : Type} {f g : Nat → α}
    (h : boundedEq N f g) : boundedEq N g f := fun i => (h i).symm
```

## \`boundedEq_trans\` (E213/Hypervisor/Lens/Instances/BoundedContext.lean)

```lean
theorem boundedEq_trans {N : Nat} {α : Type} {f g h : Nat → α}
    (hfg : boundedEq N f g) (hgh : boundedEq N g h) :
    boundedEq N f h := fun i => (hfg i).trans (hgh i)
```

## \`eventually_class_unique\` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

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

## \`limitClass_eq_tail\` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem limitClass_eq_tail {α : Type} (L : Lens α) (xs : Nat → Raw)
    (cd : CauchyData L xs) (n : Nat) (hn : n ≥ cd.N) :
    L.view (xs n) = limitClass cd := by
  unfold limitClass
  exact cd.cauchy n cd.N hn (Nat.le_refl cd.N)

/-- **Cauchy → ∃ limit class** (existential form).  Propositional
    form of CauchyData, but automatically extractable —
    `Cauchy → ∃ N witness` → CauchyData. -/
```

## \`tailCong_slash_cong\` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem tailCong_slash_cong (xs : Nat → Raw) (N : Nat)
    (x x' y y' : Raw) (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hxx' : TailCong xs N x x') (hyy' : TailCong xs N y y') :
    TailCong xs N (Raw.slash x y hxy) (Raw.slash x' y' hx'y') :=
  TailCong.slash_cong hxy hx'y' hxx' hyy'

/-- **Limit Lens**: the universalLens of TailCong is the limit Lens of
    the sequence.  Integration of Q37.3 + Cauchy completeness. -/
```

## \`limitLens_kernel\` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem limitLens_kernel (xs : Nat → Raw) (N : Nat) (r r' : Raw) :
    (limitLens xs N).view r = (limitLens xs N).view r'
      ↔ TailCong xs N r r' := by
  apply universalLens_kernel_eq_E
  · exact fun x => TailCong.refl x
  · exact fun _ _ h => TailCong.symm h
  · exact fun _ _ _ h1 h2 => TailCong.trans h1 h2
  · exact fun _ _ _ _ hxy hx'y' h1 h2 =>
      TailCong.slash_cong hxy hx'y' h1 h2

/-- **Tail collapse**: all tail elements (xs m, xs k) (m, k ≥ N)
    form a single class under limitLens.  Core expression of Cauchy
    completeness. -/
```

## \`entryEq_refl\` (E213/Hypervisor/Lens/Instances/CochainEntry.lean)

```lean
theorem entryEq_refl {N : Nat} (σ : Fin N → Bool) : entryEq σ σ :=
  fun _ => rfl
```

## \`entryEq_symm\` (E213/Hypervisor/Lens/Instances/CochainEntry.lean)

```lean
theorem entryEq_symm {N : Nat} {σ τ : Fin N → Bool}
    (h : entryEq σ τ) : entryEq τ σ := fun i => (h i).symm
```

## \`entryEq_trans\` (E213/Hypervisor/Lens/Instances/CochainEntry.lean)

```lean
theorem entryEq_trans {N : Nat} {σ τ ρ : Fin N → Bool}
    (hστ : entryEq σ τ) (hτρ : entryEq τ ρ) : entryEq σ ρ :=
  fun i => (hστ i).trans (hτρ i)
```

## \`pointwiseEq_refl\` (E213/Hypervisor/Lens/Instances/PointwiseProjection.lean)

```lean
theorem pointwiseEq_refl (f : Nat → Nat → Bool) : pointwiseEq f f :=
  fun _ _ => rfl
```

## \`pointwiseEq_symm\` (E213/Hypervisor/Lens/Instances/PointwiseProjection.lean)

```lean
theorem pointwiseEq_symm {f g : Nat → Nat → Bool}
    (h : pointwiseEq f g) : pointwiseEq g f :=
  fun m k => (h m k).symm
```

## \`pointwiseEq_trans\` (E213/Hypervisor/Lens/Instances/PointwiseProjection.lean)

```lean
theorem pointwiseEq_trans {f g h : Nat → Nat → Bool}
    (hfg : pointwiseEq f g) (hgh : pointwiseEq g h) : pointwiseEq f h :=
  fun m k => (hfg m k).trans (hgh m k)
```

## \`subtypeCombine_comm\` (E213/Hypervisor/Lens/Instances/SubtypeClosed.lean)

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

## \`slash_cong_is_lens_kernel\` (E213/Hypervisor/Lens/Kernel/Corresp.lean)

```lean
theorem slash_cong_is_lens_kernel
    (E : Raw → Raw → Prop) (h : IsSlashCongruence E)
    (r r' : Raw) :
    (universalLens E).view r = (universalLens E).view r' ↔ E r r' :=
  universalLens_kernel_eq_E E h.1 h.2.1 h.2.2.1 h.2.2.2 r r'

/-- **Bijection statement**: K = {Lens kernels (commutative-combine
    Lenses only)} = {slash-congruences}.

    Formal version: conjunction of the two directions.  Direction 1:
    every commutative-combine Lens kernel is a slash-cong;
    Direction 2: every slash-cong is realized as the kernel of a
    universalLens. -/
```

## \`kernel_correspondence\` (E213/Hypervisor/Lens/Kernel/Corresp.lean)

```lean
theorem kernel_correspondence
    (E : Raw → Raw → Prop) :
    (IsSlashCongruence E ↔
      ∀ r r', (universalLens E).view r = (universalLens E).view r' ↔ E r r') := by
  refine ⟨fun hslash r r' => slash_cong_is_lens_kernel E hslash r r', ?_⟩
  intro hbi
  -- universalLens E.equiv = E (by hbi).  And (universalLens E).equiv is a slash-cong
  -- by lens_kernel_is_slash_cong with universalLens_combine_sym.
  have hLcong : IsSlashCongruence (universalLens E).equiv :=
    lens_kernel_is_slash_cong _ (universalLens_combine_sym E)
  -- E = (universalLens E).equiv  by hbi
  have hext : (universalLens 
... [truncated]
```

## \`swap_invariant_kernel_swap_closed\` (E213/Hypervisor/Lens/Kernel/SwapInvariant.lean)

```lean
theorem swap_invariant_kernel_swap_closed {α : Type} (L : Lens α)
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    ∀ r r' : Raw, L.equiv r r' → L.equiv (Raw.swap r) (Raw.swap r') := by
  intro r r' hrr'
  show L.view (Raw.swap r) = L.view (Raw.swap r')
  rw [hinv r, hinv r']
  exact hrr'
```
