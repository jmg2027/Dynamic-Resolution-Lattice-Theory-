# Cluster `simp_users` — 130 decls (sample limited to 40)

(Auto-extracted by `tools/theorem_inspect.py`.)

## `block_constant_implies_aut_invariant` (E213/App/Simplex.lean)

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

## `Tree` (E213/Firmware/Raw/Hom.lean)

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

## `Tree` (E213/Firmware/Raw/Levels.lean)

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

## `Tree` (E213/Firmware/Raw/Signed.lean)

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

## `Raw` (E213/Firmware/RawSwap.lean)

```lean
theorem Raw.swap_injective_fn : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective h
```

## `signed_R4` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
theorem signed_R4 :
    SwapMatching signedLens (fun n : Int => -n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u; simp
  · intro h
    have : (-(1 : Int)) = (1 : Int) := by
      have := congrFun h (1 : Int); exact this
    exact absurd this (by decide)
  · intro r
    exact signed_swap_neg r

/-- Swap-invariant Lenses fail R4 pointwise: if
    `view (swap r) = view r` for all `r`, then any R4-candidate
    `conj` must fix every image point of `view`. -/
```

## `swap_invariant_of_base_eq_comm` (E213/Hypervisor/Lens/Characterisation/Core.lean)

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

## `boolToConstLens_xor` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem boolToConstLens_xor (x y : Bool) :
    boolToConstLens (xor x y) =
      lensXor (boolToConstLens x) (boolToConstLens y) := by
  cases x <;> cases y <;>
    simp [boolToConstLens, lensXor_TT, lensXor_TF, lensXor_FT, lensXor_FF]
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

## `caseElement_disjoint` (E213/Hypervisor/Lens/Instances/Prism.lean)

```lean
theorem caseElement_disjoint (target1 target2 : Raw) (h : target1 ≠ target2)
    (r : Raw) :
    ¬ ((caseElement target1).preview r = some () ∧
       (caseElement target2).preview r = some ()) := by
  intro ⟨h1, h2⟩
  unfold caseElement at h1 h2
  show False
  -- preview r = if r = target then some () else none.
  by_cases ht1 : r = target1
  · -- r = target1.
    by_cases ht2 : r = target2
    · -- r = target2 also.  target1 = target2 contradiction.
      rw [← ht1, ht2] at h
      exact h rfl
    · -- r ≠ target2 → preview target2 r = none → contradicts h2.
      simp [ht2] at h2
  · -- r ≠
... [truncated]
```

## `sumCombine_comm` (E213/Hypervisor/Lens/Instances/Sum.lean)

```lean
theorem sumCombine_comm {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (x y : Sum α β) :
    sumCombine x y = sumCombine y x := by
  cases x <;> cases y <;> simp [sumCombine, d_α.combine_sym, d_β.combine_sym]
```

## `sum_not_coproduct_xor` (E213/Hypervisor/Lens/Instances/SumNotCoproduct.lean)

```lean
theorem sum_not_coproduct_xor :
    ¬ ∃ h : Sum Bool Bool → Bool,
      (∀ x, h (Sum.inl x) = x) ∧
      (∀ x, h (Sum.inr x) = x) ∧
      (∀ x y, h (@sumCombine Bool Bool boolXorHasDistinguishing
                              boolXorHasDistinguishing x y)
              = xor (h x) (h y)) := by
  rintro ⟨h, hl, hr, hcomb⟩
  have h1 : h (Sum.inl true) = true := hl true
  have h2 : h (Sum.inr true) = true := hr true
  have h3 : @sumCombine Bool Bool boolXorHasDistinguishing
              boolXorHasDistinguishing (Sum.inl true) (Sum.inr true)
            = Sum.inl true := by
    unfold sumCombine;
... [truncated]
```

## `sum_not_coproduct_and` (E213/Hypervisor/Lens/Instances/SumNotCoproductGeneric.lean)

```lean
theorem sum_not_coproduct_and :
    ¬ ∃ h : Sum Bool Bool → Bool,
      (∀ x, h (Sum.inl x) = x) ∧
      (∀ x, h (Sum.inr x) = x) ∧
      (∀ x y, h (@sumCombine Bool Bool boolXorHasDistinguishing
                              boolXorHasDistinguishing x y)
              = (h x && h y)) := by
  rintro ⟨h, hl, hr, hcomb⟩
  have h1 : h (Sum.inl true) = true := hl true
  have h2 : h (Sum.inr false) = false := hr false
  have h3 : @sumCombine Bool Bool boolXorHasDistinguishing
              boolXorHasDistinguishing (Sum.inl true) (Sum.inr false)
            = Sum.inl true := by
    unfold sumCombine
... [truncated]
```

## `tierLens` (E213/Hypervisor/Lens/Leaves/DepthJoin.lean)

```lean
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
```

## `leavesMod3Lens_view_eq` (E213/Hypervisor/Lens/Leaves/Mod3.lean)

```lean
theorem leavesMod3Lens_view_eq :
    ∀ r : Raw, (leavesMod3Lens.view r).val = Lens.leaves.view r % 3 := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfsM : leavesMod3Lens.view (Raw.slash x y h)
                    = f3add (leavesMod3Lens.view x) (leavesMod3Lens.view y) :=
        Raw.fold_slash _ _ _ f3add_comm x y h
      have hfsN : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsM, hfsN]
  
... [truncated]
```

## `boolToProp_and` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem boolToProp_and (x y : Bool) :
    boolToProp (Bool.and x y) = (boolToProp x ∧ boolToProp y) := by
  unfold boolToProp
  cases x <;> cases y <;> simp
```

## `boolToProp_xor` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem boolToProp_xor (x y : Bool) :
    boolToProp (xor x y) = propXor (boolToProp x) (boolToProp y) := by
  unfold boolToProp propXor
  cases x <;> cases y <;> simp [xor]

/-- **Functorial commutativity (Xor pair)**: the universalMorphism of
    the Bool (xor) instance commutes with that of Prop (Xor)
    via boolToProp. -/
```

## `boolToProp_or` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem boolToProp_or (x y : Bool) :
    boolToProp (Bool.or x y) = (boolToProp x ∨ boolToProp y) := by
  unfold boolToProp
  cases x <;> cases y <;> simp

/-- **Functorial commutativity (Or pair)**. -/
```

## `boolToProp_iff` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem boolToProp_iff (x y : Bool) :
    boolToProp (decide (x = y)) = (boolToProp x ↔ boolToProp y) := by
  unfold boolToProp
  cases x <;> cases y <;> simp

/-- **Functorial commutativity (Iff pair)**. -/
```

## `leafLens_view_eq` (E213/Hypervisor/Lens/Properties/Leaf.lean)

```lean
theorem leafLens_view_eq :
    ∀ r : Raw, leafLens.view r = decide (Lens.leaves.view r ≥ 2) := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfsL : leafLens.view (Raw.slash x y h) = true := by
        apply Raw.fold_slash
        intro u v; rfl
      have hfsN : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hx := leaves_ge_one x
      have hy := leaves_ge_one y
      rw [hfsL, hfsN]
     
... [truncated]
```

## `eight_eq_two_nTsq` (E213/Kernel/Cap_PeriodicTable.lean)

```lean
theorem eight_eq_two_nTsq :
    eval (mul (succ (succ zero)) (mul nT nT)) = 8 := rfl

/-- period 1 length = 2 = n_T (He, the simplest closure). -/
```

## `parity` (E213/Kernel/Tactic/Mod213.lean)

```lean
def parity : Nat → Bool
  | 0     => false
  | 1     => true
  | n + 2 => parity n

@[simp] theorem parity_step (n : Nat) : parity (n + 2) = parity n := rfl
@[simp] theorem parity_zero : parity 0 = false := rfl
@[simp] theorem parity_one : parity 1 = true := rfl
```

## `mod3` (E213/Kernel/Tactic/Mod213.lean)

```lean
def mod3 : Nat → Nat
  | 0     => 0
  | 1     => 1
  | 2     => 2
  | n + 3 => mod3 n

@[simp] theorem mod3_step (n : Nat) : mod3 (n + 3) = mod3 n := rfl
@[simp] theorem mod3_zero : mod3 0 = 0 := rfl
@[simp] theorem mod3_one  : mod3 1 = 1 := rfl
@[simp] theorem mod3_two  : mod3 2 = 2 := rfl

/-- Bound: `mod3 n < 3` — ∅-axiom via `Nat.le.step` chain. -/
```

## `parity_add` (E213/Kernel/Tactic/Mod213.lean)

```lean
theorem parity_add : ∀ n m : Nat, parity (n + m) = (parity n != parity m)
  | n, 0     => by show parity n = (parity n != false); cases parity n <;> rfl
  | n, 1     => by
      show parity (n + 1) = (parity n != true)
      have hps : parity (n + 1) = !parity n := parity_succ n
      have aux : (!parity n) = (parity n != true) := by cases parity n <;> rfl
      exact hps.trans aux
  | n, m + 2 => parity_add n m

/-- `parity (2^0) = parity 1 = true`.  Single base case. -/
@[simp] theorem parity_pow_two_zero : parity (2^0) = true := rfl

/-- `parity (2^(k+1)) = false`.  Trajectory completed at 
... [truncated]
```

## `peanoLens` (E213/Math/AxiomSystems/PeanoAsLensComposition.lean)

```lean
def peanoLens : Lens Nat := Lens.leaves

/-- Peano's "successor of zero" — the simplest non-trivial Raw
    expression viewed as Nat: a single base element = 1.
    (Peano: succ(0) = 1.) -/
```

## `orderCauchy_is_GFCauchy` (E213/Math/Cauchy/GenericFamily.lean)

```lean
theorem orderCauchy_is_GFCauchy
    (xs : Nat → Raw)
    (h : E213.Math.Cauchy.Archimedean.isOrderCauchy xs) :
    GFCauchy E213.Hypervisor.Lens.Instances.AB.abLens
      (fun (mk : Nat × Nat) (p : Nat × Nat) =>
         E213.Math.Cauchy.Archimedean.orderProj mk.1 mk.2 p) xs := by
  intro mk
  by_cases hk : mk.2 ≥ 1
  · obtain ⟨N, hN⟩ := h mk.1 mk.2 hk
    exact ⟨N, hN⟩
  · -- mk.2 = 0: orderProj is always true (since p.1 * 0 = 0 ≤ p.2 * mk.1)
    refine ⟨0, ?_⟩
    intro k l _ _
    show E213.Math.Cauchy.Archimedean.orderProj mk.1 mk.2 _ =
         E213.Math.Cauchy.Archimedean.orderProj mk.1 
... [truncated]
```

## `factorial_pos` (E213/Math/Cauchy/ProfiniteSeq.lean)

```lean
theorem factorial_pos (n : Nat) : factorial n ≥ 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      show (k+1) * factorial k ≥ 1
      have := Nat.mul_le_mul_left (k+1) ih
      simp at this
      omega

/-- factorial n is divisible by every m ≤ n. -/
```

## `conj` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
def conj (u : Sedenion) : Sedenion := ⟨u.re.conj, -u.im⟩

-- ═══ Projection simp lemmas for hurwitz_ring ═══
```

## `normSq` (E213/Math/CayleyDickson/ZI.lean)

```lean
def normSq (u : ZI) : Int := u.re * u.re + u.im * u.im

-- ═══ Basic structural lemmas ═══

@[simp] theorem re_zero : (0 : ZI).re = 0 := rfl
@[simp] theorem im_zero : (0 : ZI).im = 0 := rfl
```

## `conj_conj` (E213/Math/CayleyDickson/ZI.lean)

```lean
theorem conj_conj (u : ZI) : u.conj.conj = u := by
  apply ext <;> simp [conj]
```

## `normSq_eq_zero_iff` (E213/Math/CayleyDickson/ZIDomain.lean)

```lean
theorem normSq_eq_zero_iff (u : ZI) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    have h_eq : u.re * u.re + u.im * u.im = 0 := h
    have hre : u.re * u.re = 0 := by omega
    have him : u.im * u.im = 0 := by omega
    apply ext
    · exact IntHelpers.mul_self_eq_zero.mp hre
    · exact IntHelpers.mul_self_eq_zero.mp him
  · rintro rfl
    show (0 : Int) * 0 + 0 * 0 = 0
    simp

/-- **Integral-domain property.** `ZI.mul` has no zero divisors. -/
```

## `no_zero_div` (E213/Math/CayleyDickson/ZIDomain.lean)

```lean
theorem no_zero_div (u v : ZI) : u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 + 0 * 0 = 0; simp
  rw [normSq_mul] at hn
  rcases Int.mul_eq_zero.mp hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff v).mp h)
```

## `conj_negI` (E213/Math/CayleyDickson/ZIHom.lean)

```lean
theorem conj_negI : ZI.conj negI = I := by
  show (⟨0, -(-1)⟩ : ZI) = ⟨0, 1⟩
  apply ext <;> simp

/-- `conj` distributes over Gaussian multiplication. -/
```

## `normSq` (E213/Math/CayleyDickson/ZOmega.lean)

```lean
def normSq (u : ZOmega) : Int :=
  u.re * u.re - u.re * u.im + u.im * u.im

@[simp] theorem re_zero : (0 : ZOmega).re = 0 := rfl
@[simp] theorem im_zero : (0 : ZOmega).im = 0 := rfl
```

## `conj_Omega2` (E213/Math/CayleyDickson/ZOmega.lean)

```lean
theorem conj_Omega2 : conj Omega2 = Omega := by
  show (⟨-1 - -1, -(-1)⟩ : ZOmega) = ⟨0, 1⟩
  apply ext <;> simp
```

## `conj_mul` (E213/Math/CayleyDickson/ZOmegaDomain.lean)

```lean
theorem conj_mul (u v : ZOmega) :
    conj (u * v) = conj u * conj v := by
  apply ext
  · show (u.re*v.re - u.im*v.im)
        - (u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(v.re - v.im) - (-u.im)*(-v.im)
    simp only [Int.sub_mul, Int.mul_sub, Int.neg_mul,
               Int.mul_neg, Int.neg_neg]
    omega
  · show -(u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(-v.im) + (-u.im)*(v.re - v.im)
         - (-u.im)*(-v.im)
    simp only [Int.sub_mul, Int.mul_sub, Int.neg_mul,
               Int.mul_neg, Int.neg_neg]
    omega
```
