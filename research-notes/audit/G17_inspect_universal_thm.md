# Cluster universal_thm — 618 decls (sample 50)

## \`getBase_eq\` (E213/Firmware/Atomicity/ArityForcingGeneral.lean)

```lean
theorem getBase_eq {N k : Nat} :
    ∀ (x : RawNk N k) (h : isBase x = true), x = .object (getBase x h)
  | .object _, _ => rfl
  | .rel _,    h => by cases h
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

## \`RawBy_bijection\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem RawBy_bijection (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    ∀ (r : RawBy cmp2),
        transportRawBy cmp1 cmp2 h1 h2
          (transportRawBy cmp2 cmp1 h2 h1 r) = r :=
  transportRawBy_roundtrip cmp1 cmp2 h1 h2
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

## \`swap_invariant_base_eq\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
theorem swap_invariant_base_eq {α : Type} {L : Hypervisor.Lens α}
    (h : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    L.base_a = L.base_b := by
  have h0 := h Raw.a
  rw [Raw.swap_a] at h0
  -- h0 : L.view Raw.b = L.view Raw.a
  -- both sides reduce by computation
  exact h0.symm
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

## \`swap_invariant_of_base_eq_comm\` (E213/Hypervisor/Lens/Characterisation/Core.lean)

```lean
theorem swap_invariant_of_base_eq_comm
    {α : Type} (L : Hypervisor.Lens α)
    (hbase : L.base_a = L.base_b)
    (hcomm : ∀ u v : α, L.combine u v = L.combine v u)
    (r : Raw) : L.view (Raw.swap r) = L.view r := by
  show Raw.fold L.base_a L.base_b L.combine (Raw.swap r)
     = Raw.fold L.base_a L.base_b L.combine r
  have h := Raw.fold_swap_hom L.base_a L.base_b L.combine id
    (by simp [hbase]) (by simp [hbase])
    (fun _ _ => rfl) hcomm r
  exact h
```

## \`swap_invariant_iff_base_eq_of_comm\` (E213/Hypervisor/Lens/Characterisation/Core.lean)

```lean
theorem swap_invariant_iff_base_eq_of_comm
    {α : Type} (L : Hypervisor.Lens α)
    (hcomm : ∀ u v : α, L.combine u v = L.combine v u) :
    (∀ r : Raw, L.view (Raw.swap r) = L.view r)
      ↔ L.base_a = L.base_b := by
  constructor
  · intro h
    exact swap_invariant_base_eq h
  · intro hbase r
    exact swap_invariant_of_base_eq_comm L hbase hcomm r

-- ═══ Characterisation 2: conj uniqueness on image ═══

/-- **R4 uniqueness on image.**  If two involutions both
    witness R4 for the same Lens, they coincide on every
    value in the view-image (not necessarily on all of α).
    Proof by
... [truncated]
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

## \`abLens_sum_eq_leaves\` (E213/Hypervisor/Lens/Instances/AB.lean)

```lean
theorem abLens_sum_eq_leaves :
    ∀ r : Raw, (abLens.view r).1 + (abLens.view r).2 = Lens.leaves.view r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfsA : abLens.view (Raw.slash x y h)
                    = abLens.combine (abLens.view x) (abLens.view y) :=
        Raw.fold_slash _ _ _ abLens_sym x y h
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsA, hfsL]
      show (a
... [truncated]
```

## \`bool_not_involutive\` (E213/Hypervisor/Lens/Instances/Bool.lean)

```lean
theorem bool_not_involutive : ∀ u : Bool, !(!u) = u := by decide

/-- `not` on Bool is NOT the identity. -/
```

## \`boolXorLens_not_homomorphism\` (E213/Hypervisor/Lens/Instances/Bool.lean)

```lean
theorem boolXorLens_not_homomorphism :
    ¬ (∀ u v : Bool, !(xor u v) = xor (!u) (!v)) := by
  intro h
  have := h true false
  -- `!(true xor false) = xor (!true) (!false) = xor false true`
  -- LHS = !true = false; RHS = xor false true = true
  revert this; decide
```

## \`limitLens_is_least\` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem limitLens_is_least {α : Type} (N : Lens α)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (xs : Nat → Raw) (M : Nat)
    (hCollapse : ∀ m k, m ≥ M → k ≥ M → N.equiv (xs m) (xs k)) :
    (limitLens xs M).refines N := by
  intro r r' h
  have hTC : TailCong xs M r r' := (limitLens_kernel xs M r r').mp h
  exact tailCong_implies_equiv N hNsym xs M hCollapse r r' hTC
```

## \`F3\` (E213/Hypervisor/Lens/Instances/F9.lean)

```lean
abbrev F3 := Fin 3
```

## \`F9\` (E213/Hypervisor/Lens/Instances/F9.lean)

```lean
abbrev F9 := F3 × F3
```

## \`idLens_symmetric\` (E213/Hypervisor/Lens/Instances/Identity.lean)

```lean
theorem idLens_symmetric :
    ∀ u v : Raw, idLens.combine u v = idLens.combine v u := by
  intro u v
  by_cases h : u = v
  · rw [h]
  · show (if h : u ≠ v then Raw.slash u v h else Raw.a)
         = (if h : v ≠ u then Raw.slash v u h else Raw.a)
    rw [dif_pos h, dif_pos (Ne.symm h)]
    exact Raw.slash_comm u v h
```

## \`idLens_is_id\` (E213/Hypervisor/Lens/Instances/Identity.lean)

```lean
theorem idLens_is_id : ∀ r : Raw, idLens.view r = r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : idLens.view (Raw.slash x y h)
                   = idLens.combine (idLens.view x) (idLens.view y) :=
        Raw.fold_slash idLens.base_a idLens.base_b idLens.combine
          idLens_symmetric x y h
      rw [hfs, ihx, ihy]
      show (if h' : x ≠ y then Raw.slash x y h' else Raw.a)
           = Raw.slash x y h
      rw [dif_pos h]
```

## \`negSqLens_symmetric\` (E213/Hypervisor/Lens/Instances/NegSq.lean)

```lean
theorem negSqLens_symmetric :
    ∀ u v : Bool, negSqLens.combine u v = negSqLens.combine v u := by
  intro u v; cases u <;> cases v <;> rfl
```

## \`joinEquiv_parityLens_boolXorLens_universal\` (E213/Hypervisor/Lens/Instances/ParityXorJoin.lean)

```lean
theorem joinEquiv_parityLens_boolXorLens_universal :
    ∀ r r' : Raw, JoinEquiv parityLens boolXorLens r r' := by
  intro r r'
  exact JoinEquiv.trans (join_to_a r) (JoinEquiv.symm (join_to_a r'))

/-- **Consequence**: any symmetric-combine Lens refining both
    parityLens and boolXorLens is constant.  (Applying
    JoinEquiv_is_least.) -/
```

## \`refine_parity_boolXor_implies_const\` (E213/Hypervisor/Lens/Instances/ParityXorJoin.lean)

```lean
theorem refine_parity_boolXor_implies_const {γ : Type} (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLp : parityLens.refines N) (hLb : boolXorLens.refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  exact JoinEquiv_is_least parityLens boolXorLens N hNsym hLp hLb r r'
    (joinEquiv_parityLens_boolXorLens_universal r r')
```

## \`joinEquiv_leavesLens_boolXorLens_universal\` (E213/Hypervisor/Lens/Instances/ParityXorJoin.lean)

```lean
theorem joinEquiv_leavesLens_boolXorLens_universal :
    ∀ r r' : Raw, JoinEquiv Lens.leaves boolXorLens r r' := by
  intro r r'
  exact JoinEquiv.trans (leavesLens_to_a r)
    (JoinEquiv.symm (leavesLens_to_a r'))

/-- **Consequence**: any symmetric-combine Lens refining both leaves
    and boolXorLens is constant. -/
```

## \`refine_leaves_boolXor_implies_const\` (E213/Hypervisor/Lens/Instances/ParityXorJoin.lean)

```lean
theorem refine_leaves_boolXor_implies_const {γ : Type} (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLl : Lens.leaves.refines N) (hLb : boolXorLens.refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  exact JoinEquiv_is_least Lens.leaves boolXorLens N hNsym hLl hLb r r'
    (joinEquiv_leavesLens_boolXorLens_universal r r')
```

## \`pathLens_combine_not_commutative\` (E213/Hypervisor/Lens/Instances/Path.lean)

```lean
theorem pathLens_combine_not_commutative :
    ¬ ∀ u v : List Bool, pathLens.combine u v = pathLens.combine v u := by
  intro h
  have := h [false] [true]
  -- `this : [false, true] = [true, false]`
  revert this; decide

-- ═══ R5 — injectivity holds on level-≤2 (the 5 Raw terms) ═══

/-- The 5 Raw terms of level ≤ 2 have 5 distinct list-views,
    so `pathLens.view` is injective on this finite subset. -/
example :
    pathLens.view Raw.a
      ≠ pathLens.view Raw.b := by decide
example :
    pathLens.view Raw.a
      ≠ pathLens.view (Raw.slash Raw.a Raw.b (by decide)) := by decide
example :

... [truncated]
```

## \`rawACharLens_view_eq\` (E213/Hypervisor/Lens/Instances/RawAChar.lean)

```lean
theorem rawACharLens_view_eq :
    ∀ r : Raw, rawACharLens.view r = decide (r = Raw.a) := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : rawACharLens.view (Raw.slash x y h)
                   = rawACharLens.combine
                       (rawACharLens.view x) (rawACharLens.view y) := by
        apply Raw.fold_slash
        intro _ _; rfl
      rw [hfs]
      show (false : Bool) = decide (Raw.slash x y h = Raw.a)
      have hne : Raw.slash x y h ≠ Raw.a := by
        intro heq
        have hv : (Raw.slash x y h).val = Ra
... [truncated]
```

## \`rawMatching_view_is_id\` (E213/Hypervisor/Lens/Instances/RawMatching.lean)

```lean
theorem rawMatching_view_is_id (L : Lens Raw)
    (hba : L.base_a = Raw.a)
    (hbb : L.base_b = Raw.b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              L.combine x y = Raw.slash x y h)
    (hsym : ∀ u v : Raw, L.combine u v = L.combine v u) :
    ∀ r : Raw, L.view r = r := by
  intro r
  induction r using Raw.rec with
  | a =>
      show L.base_a = Raw.a
      exact hba
  | b =>
      show L.base_b = Raw.b
      exact hbb
  | slash x y h ihx ihy =>
      have hfs : L.view (Raw.slash x y h)
                   = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hsym x y h
  
... [truncated]
```

## \`swapLens_view_eq_swap\` (E213/Hypervisor/Lens/Instances/Swap.lean)

```lean
theorem swapLens_view_eq_swap : ∀ r : Raw, swapLens.view r = Raw.swap r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : swapLens.view (Raw.slash x y h)
                   = swapLens.combine (swapLens.view x) (swapLens.view y) :=
        Raw.fold_slash _ _ _ swapLens_symmetric x y h
      rw [hfs, ihx, ihy]
      have hne : Raw.swap x ≠ Raw.swap y :=
        fun e => h (Raw.swap_injective e)
      show (if h' : Raw.swap x ≠ Raw.swap y then
              Raw.slash (Raw.swap x) (Raw.swap y) h'
            else Raw.a)
         
... [truncated]
```

## \`swapLens_view_involutive\` (E213/Hypervisor/Lens/Instances/Swap.lean)

```lean
theorem swapLens_view_involutive :
    ∀ r : Raw, swapLens.view (swapLens.view r) = r := by
  intro r
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap, Raw.swap_swap]

/-- swapLens has an injective view (since it is involutive). -/
```

## \`zmod6Lens_combine_comm\` (E213/Hypervisor/Lens/Instances/ZMod6.lean)

```lean
theorem zmod6Lens_combine_comm :
    ∀ u v : Nat, zmod6Lens.combine u v = zmod6Lens.combine v u := by
  intro u v
  show (u * v) % 6 = (v * u) % 6
  rw [Nat.mul_comm]

/-- Every Raw `r ≠ Raw.a` whose construction passes through
    `Raw.slash a b` inherits view `0`: the R3-failure zero
    absorbs.  Concrete two-witness case:
    `slash a (slash a b)` and `slash b (slash a b)` both
    have view `0`, giving a second R5-injectivity failure. -/
example :
    zmod6Lens.view (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide))
        (by decide))
      = zmod6Lens.view (Raw.slash Raw.b (Raw.slash
... [truncated]
```

## \`Lens\` (E213/Hypervisor/Lens/Kernel/Congruence.lean)

```lean
theorem Lens.equiv_slash_congruence {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x x' y y' : Raw) (hx : x ≠ y) (hx' : x' ≠ y')
    (hxx' : L.equiv x x') (hyy' : L.equiv y y') :
    L.equiv (Raw.slash x y hx) (Raw.slash x' y' hx') := by
  show L.view (Raw.slash x y hx) = L.view (Raw.slash x' y' hx')
  have hf1 : L.view (Raw.slash x y hx)
               = L.combine (L.view x) (L.view y) :=
    Raw.fold_slash _ _ _ hsym x y hx
  have hf2 : L.view (Raw.slash x' y' hx')
               = L.combine (L.view x') (L.view y') :=
    Raw.fold_slash _ _ _ hsym x' y' hx
... [truncated]
```

## \`lens_kernel_is_slash_cong\` (E213/Hypervisor/Lens/Kernel/Corresp.lean)

```lean
theorem lens_kernel_is_slash_cong {α : Type} (L : Lens α)
    (hsym : ∀ u v, L.combine u v = L.combine v u) :
    IsSlashCongruence (L.equiv) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; rfl
  · intro r r' h; exact h.symm
  · intro r r' r'' h1 h2; exact h1.trans h2
  · intros x x' y y' h h' hxx hyy
    exact Kernel.Congruence.Lens.equiv_slash_congruence L hsym
      x x' y y' h h' hxx hyy
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

## \`swap_invariant_equates_orbit\` (E213/Hypervisor/Lens/Kernel/SwapInvariant.lean)

```lean
theorem swap_invariant_equates_orbit {α : Type} (L : Lens α)
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    ∀ r : Raw, L.equiv r (Raw.swap r) := by
  intro r
  show L.view r = L.view (Raw.swap r)
  exact (hinv r).symm

/-- A swap-invariant Lens has a swap-invariant kernel:
    r ~ r' ↔ swap r ~ swap r'. -/
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

## \`familyMeet_refl\` (E213/Hypervisor/Lens/Lattice/FamilyMeet.lean)

```lean
theorem familyMeet_refl {I : Type} (E : I → Raw → Raw → Prop)
    (hrefl : ∀ i r, E i r r) (r : Raw) : familyMeet E r r :=
  fun i => hrefl i r
```

## \`familyMeet_symm\` (E213/Hypervisor/Lens/Lattice/FamilyMeet.lean)

```lean
theorem familyMeet_symm {I : Type} (E : I → Raw → Raw → Prop)
    (hsymm : ∀ i r r', E i r r' → E i r' r) (r r' : Raw) :
    familyMeet E r r' → familyMeet E r' r :=
  fun h i => hsymm i r r' (h i)
```

## \`familyMeet_trans\` (E213/Hypervisor/Lens/Lattice/FamilyMeet.lean)

```lean
theorem familyMeet_trans {I : Type} (E : I → Raw → Raw → Prop)
    (htrans : ∀ i r r' r'', E i r r' → E i r' r'' → E i r r'')
    (r r' r'' : Raw) :
    familyMeet E r r' → familyMeet E r' r'' → familyMeet E r r'' :=
  fun h1 h2 i => htrans i r r' r'' (h1 i) (h2 i)
```
