# Cluster equality_other — 246 decls (sample 40)

## \`bezout_left\` (E213/Firmware/Atomicity/FiveHelpers.lean)

```lean
theorem bezout_left {a b : Nat} (ha : 3 ≤ a) :
    2 * a + 3 * b = 2 * (a - 3) + 3 * (b + 2) := by
  have h1 : 2 * (a - 3) = 2 * a - 6 := mul_sub_distrib ha
  have h2 : 3 * (b + 2) = 3 * b + 6 := Nat.mul_add 3 b 2
  have h6 : 6 ≤ 2 * a := Nat.mul_le_mul_left 2 ha
  have step1 : (2 * a - 6) + (3 * b + 6) = (2 * a - 6) + (6 + 3 * b) :=
    congrArg (2 * a - 6 + ·) (Nat.add_comm (3 * b) 6)
  have step2 : (2 * a - 6) + (6 + 3 * b) = ((2 * a - 6) + 6) + 3 * b :=
    (Nat.add_assoc _ _ _).symm
  have step3 : (2 * a - 6) + 6 = 2 * a := sub_add_cancel h6
  have step4 : ((2 * a - 6) + 6) + 3 * b = 2 * 
... [truncated]
```

## \`bezout_right\` (E213/Firmware/Atomicity/FiveHelpers.lean)

```lean
theorem bezout_right {a b : Nat} (hb : 2 ≤ b) :
    2 * a + 3 * b = 2 * (a + 3) + 3 * (b - 2) := by
  have h1 : 2 * (a + 3) = 2 * a + 6 := Nat.mul_add 2 a 3
  have h2 : 3 * (b - 2) = 3 * b - 6 := mul_sub_distrib hb
  have h6 : 6 ≤ 3 * b := Nat.mul_le_mul_left 3 hb
  have step1 : (2 * a + 6) + (3 * b - 6) = 2 * a + (6 + (3 * b - 6)) :=
    Nat.add_assoc _ _ _
  have step2 : 6 + (3 * b - 6) = (3 * b - 6) + 6 := Nat.add_comm _ _
  have step3 : (3 * b - 6) + 6 = 3 * b := sub_add_cancel h6
  have step4 : 2 * a + (6 + (3 * b - 6)) = 2 * a + 3 * b :=
    congrArg (2 * a + ·) (step2.trans step3)
  hav
... [truncated]
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

## \`transportRawBy_roundtrip\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem transportRawBy_roundtrip
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (r : RawBy cmp2) :
    transportRawBy cmp1 cmp2 h1 h2
      (transportRawBy cmp2 cmp1 h2 h1 r) = r := by
  apply Subtype.ext
  show transportTree cmp2 (transportTree cmp1 r.val) = r.val
  exact transportTree_roundtrip cmp1 cmp2 h1 h2 r.val r.property

/-- **Final**: RawBy cmp1 ≃ RawBy cmp2 (inverse via roundtrip).
    Formal closing of the cmp-independence meta theorem. -/
```

## \`Raw\` (E213/Firmware/Raw/Levels.lean)

```lean
theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property
```

## \`Raw\` (E213/Firmware/Raw/Signed.lean)

```lean
theorem Raw.fold_signed_swap (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r :=
  Tree.fold_signed_swap r.val r.property
```

## \`Raw\` (E213/Firmware/Raw/Swap.lean)

```lean
def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩
```

## \`Raw\` (E213/Firmware/RawLevels.lean)

```lean
def Raw.level1_set : List Raw :=
  [Raw.a, Raw.b, Raw.slash Raw.a Raw.b (by decide)]

/-- Level-2 additions: the Raw terms `a/(a/b)`, `b/(a/b)`. -/
```

## \`Raw\` (E213/Firmware/RawSwap.lean)

```lean
theorem Raw.swap_injective_fn : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective h
```

## \`sound_lens\` (E213/Hypervisor/Lens/AxiomLenses/Bridges/QuotSound.lean)

```lean
theorem sound_lens {α : Type} (s : SetoidLens α) {a b : α}
    (h : s.rel a b) : project s a = project s b :=
  Quot.sound h
```

## \`eq_implies_iffEquiv\` (E213/Hypervisor/Lens/AxiomLenses/Core/Propext.lean)

```lean
theorem eq_implies_iffEquiv {P Q : Prop} (h : P = Q) : iffEquiv P Q :=
  h ▸ iffEquiv_refl P
```

## \`signed_swap_neg\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
theorem signed_swap_neg (r : Raw) :
    signedLens.view (Raw.swap r) = - signedLens.view r := by
  show Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
     = - Raw.fold (1 : Int) (-1) (· + ·) r
  exact Raw.fold_signed_swap r
```

## \`lensUniversalMorphism_a\` (E213/Hypervisor/Lens/Compose/OnLens.lean)

```lean
theorem lensUniversalMorphism_a :
    lensUniversalMorphism Raw.a = constTrueLens :=
  @universalMorphism_a (Lens Bool) lensBoolHasDistinguishing
```

## \`lensUniversalMorphism_b\` (E213/Hypervisor/Lens/Compose/OnLens.lean)

```lean
theorem lensUniversalMorphism_b :
    lensUniversalMorphism Raw.b = constFalseLens :=
  @universalMorphism_b (Lens Bool) lensBoolHasDistinguishing
```

## \`lensUniversalMorphism_slash\` (E213/Hypervisor/Lens/Compose/OnLens.lean)

```lean
theorem lensUniversalMorphism_slash (x y : Raw) (h : x ≠ y) :
    lensUniversalMorphism (Raw.slash x y h)
      = lensXor (lensUniversalMorphism x) (lensUniversalMorphism y) :=
  @universalMorphism_slash (Lens Bool) lensBoolHasDistinguishing x y h
```

## \`lensUniversalMorphism_factors\` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem lensUniversalMorphism_factors (r : Raw) :
    lensUniversalMorphism r = composite r := by
  have h := @universalMorphism_unique (Lens Bool) lensBoolHasDistinguishing
    composite composite_a composite_b composite_slash r
  exact h.symm
```

## \`lensUniversalMorphism_factors_generic\` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)

```lean
theorem lensUniversalMorphism_factors_generic
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    @universalMorphism (Lens α) (lensHasDistinguishing α) r =
      constComposite α r := by
  have := @universalMorphism_unique (Lens α) (lensHasDistinguishing α)
    (constComposite α)
    (constComposite_a α)
    (constComposite_b α)
    (constComposite_slash α) r
  exact this.symm
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

## \`parityXor_is_pair\` (E213/Hypervisor/Lens/Instances/CompoundBool.lean)

```lean
theorem parityXor_is_pair (r : Raw) :
    parityXorLens.view r = (parityLens.view r, boolXorLens.view r) := by
  apply Prod.ext
  · exact parityXor_fst_eq_parity r
  · exact parityXor_snd_eq_boolXor r
```

## \`raw_distinguished_by_idLens\` (E213/Hypervisor/Lens/Instances/Identity.lean)

```lean
theorem raw_distinguished_by_idLens :
    Function.Injective (fun r : Raw => Raw.eval r idLens) :=
  idLens_injective
```

## \`KernelSpace\` (E213/Hypervisor/Lens/Kernel/Space.lean)

```lean
def KernelSpace : Type := { E : Raw → Raw → Prop // IsSlashCongruence E }

/-- Two KernelSpace elements are equal iff their relations are equal. -/
```

## \`familyJoin_contains\` (E213/Hypervisor/Lens/Lattice/FamilyJoin.lean)

```lean
theorem familyJoin_contains {I : Type} (E : I → Raw → Raw → Prop)
    (i : I) (r r' : Raw) (h : E i r r') :
    (familyJoinLens E).view r = (familyJoinLens E).view r' :=
  (familyJoinLens_kernel E r r').mpr (FamilyJoinEquiv.ofI i h)
```

## \`boolToProp_false\` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)

```lean
theorem boolToProp_false : boolToProp false = False := by
  unfold boolToProp
  apply propext
  exact ⟨fun h => Bool.noConfusion h, fun h => h.elim⟩
```

## \`refinesEquiv_symm\` (E213/Hypervisor/Lens/Properties/CanonicalForm.lean)

```lean
theorem refinesEquiv_symm {α β} {L : Lens α} {M : Lens β} :
    refinesEquiv L M → refinesEquiv M L
  | ⟨h1, h2⟩ => ⟨h2, h1⟩
```

## \`universalMorphism_slash\` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)

```lean
theorem universalMorphism_slash (α : Type) [d : HasDistinguishing α]
    (x y : Raw) (h : x ≠ y) :
    universalMorphism α (Raw.slash x y h)
      = d.combine (universalMorphism α x) (universalMorphism α y) := by
  unfold universalMorphism
  apply Raw.fold_slash _ _ _ d.combine_sym
```

## \`propXor_comm\` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)

```lean
theorem propXor_comm (P Q : Prop) : propXor P Q = propXor Q P := by
  unfold propXor
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    intro h; exact h2 h.symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    intro h; exact h2 h.symm
```

## \`canonicalTruthMap_a\` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)

```lean
theorem canonicalTruthMap_a : canonicalTruthMap Raw.a = True :=
  @universalMorphism_a Prop propAsDistinguishing

/-- canonicalTruthMap b = False. -/
```

## \`canonicalTruthMap_b\` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)

```lean
theorem canonicalTruthMap_b : canonicalTruthMap Raw.b = False :=
  @universalMorphism_b Prop propAsDistinguishing

/-- canonicalTruthMap (slash x y h) = propXor (... x) (... y). -/
```

## \`universalLens_combine_sym\` (E213/Hypervisor/Lens/Universal/QuotLens.lean)

```lean
theorem universalLens_combine_sym (f g : Raw → Prop) :
    (universalLens E).combine f g = (universalLens E).combine g f := by
  funext r'
  apply propext
  constructor
  · rintro ⟨X, Y, h, hX, hY, hslashr'⟩
    refine ⟨Y, X, Ne.symm h, hY, hX, ?_⟩
    rwa [Raw.slash_comm Y X (Ne.symm h)]
  · rintro ⟨X, Y, h, hX, hY, hslashr'⟩
    refine ⟨Y, X, Ne.symm h, hY, hX, ?_⟩
    rwa [Raw.slash_comm Y X (Ne.symm h)]

/-- **Core theorem 1**: view r = (E r ·).  Raw.rec induction. -/
```

## \`of_equiv\` (E213/Kernel/Sound.lean)

```lean
theorem of_equiv {a b : Term} (h : equiv a b = true) : eval a = eval b :=
  Nat.eq_of_beq_eq_true h

/-- le_b = true → eval ≤ (less-or-equal). -/
```

## \`to_equiv\` (E213/Kernel/Sound.lean)

```lean
theorem to_equiv {a b : Term} (h : eval a = eval b) : equiv a b = true :=
  @Eq.subst Nat (fun x => Nat.beq (eval a) x = true)
    (eval a) (eval b) h (beq_refl' (eval a))

/-- Application: promotes dim_law from Demo into Lean Eq form. -/
```

## \`parity_pow_two_succ\` (E213/Kernel/Tactic/Mod213.lean)

```lean
theorem parity_pow_two_succ (k : Nat) : parity (2^(k+1)) = false :=
  Nat.pow_succ 2 k ▸ Nat.mul_comm 2 (2^k) ▸ parity_double (2^k)

/-- `parity (2^k) = false` whenever `k ≥ 1`. -/
```

## \`add_sub_of_le\` (E213/Kernel/Tactic/Nat213.lean)

```lean
theorem add_sub_of_le {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  have : n - m + m = n := sub_add_cancel h
  have hcomm : m + (n - m) = (n - m) + m := Nat.add_comm m (n - m)
  exact hcomm.trans this

/-- `(a + b) - b = a`.  ∅-axiom replacement (Lean-core
    `Nat.add_sub_cancel` proof brings propext on some forms). -/
```

## \`add_left_cancel\` (E213/Kernel/Tactic/Nat213.lean)

```lean
theorem add_left_cancel {a b c : Nat} (h : a + b = a + c) : b = c :=
  let h' : b + a = c + a := (Nat.add_comm b a).trans (h.trans (Nat.add_comm a c))
  add_right_cancel h'

/-- `a * b * c = a * (b * c)`.  ∅-axiom replacement for
    `Nat.mul_assoc` (Lean-core proof brings propext). -/
```

## \`mul_sub_distrib\` (E213/Kernel/Tactic/Nat213.lean)

```lean
theorem mul_sub_distrib {a b c : Nat} (h : b ≤ a) :
    c * (a - b) = c * a - c * b := by
  have he : (a - b) + b = a := sub_add_cancel h
  have h1 : c * ((a - b) + b) = c * (a - b) + c * b := Nat.mul_add c (a - b) b
  have h2 : c * ((a - b) + b) = c * a := congrArg (c * ·) he
  have hcdist : c * a = c * (a - b) + c * b := h2.symm.trans h1
  have hcancel : c * (a - b) + c * b - c * b = c * (a - b) :=
    add_sub_cancel_right (c * (a - b)) (c * b)
  exact hcancel.symm.trans (congrArg (· - c * b) hcdist.symm)

-- NOTE: cohomological-trajectory primitives (parity, mod3, mod6,
-- CRT pairing) live
... [truncated]
```

## \`sub_sub_self\` (E213/Kernel/Tactic/Nat213.lean)

```lean
theorem sub_sub_self {n m : Nat} (h : m ≤ n) : n - (n - m) = m :=
  let h1 : n - m + m = n := sub_add_cancel h
  let h2 : m + (n - m) = n - m + m := Nat.add_comm m (n - m)
  let h3 : m + (n - m) = n := h2.trans h1
  Eq.subst (motive := fun x => x - (n - m) = m) h3
    (add_sub_cancel_right m (n - m))

/-- `a + 1 ≤ b → 1 ≤ b - a`.  ∅-axiom (term mode) — used in
    Cauchy seq files for "n - 1 ≥ 1 when n ≥ 2" patterns. -/
```

## \`mod_add_mod\` (E213/Math/AddMod213.lean)

```lean
theorem mod_add_mod {b : Nat} (hb : 0 < b) (a c : Nat) :
    (a % b + c) % b = (a + c) % b :=
  (add_mod_left hb a c).symm

/-- `(a + b) % n = (a % n + b % n) % n` when `0 < n`.  ∅-axiom. -/
```

## \`cut_eq_tail\` (E213/Math/Cauchy/Archimedean.lean)

```lean
theorem cut_eq_tail {xs : Nat → Raw} (cd : OrderCauchyData xs)
    (m k : Nat) (hk : k ≥ 1) (n : Nat) (hn : n ≥ cd.N m k) :
    orderProj m k (abLens.view (xs n)) = cd.cut m k := by
  unfold OrderCauchyData.cut
  exact cd.cauchy m k n (cd.N m k) hk hn (Nat.le_refl _)
```

## \`eulerRaw_view\` (E213/Math/Cauchy/EulerSeq.lean)

```lean
theorem eulerRaw_view (n : Nat) :
    abLens.view (eulerRaw n).val = (eulerNum n, eulerDen n) :=
  (eulerRaw n).property

/-- **Cut above 3**: m/k ≥ 3 (3k ≤ m) → orderProj true (all n).
    a_n * k ≤ (3 d_n - 1) * k ≤ 3 d_n * k ≤ d_n * m. -/
```

## \`limitAssign_eq_tail\` (E213/Math/Cauchy/GenericFamily.lean)

```lean
theorem limitAssign_eq_tail {α β : Type} {ι : Type}
    {L : Lens α} {F : ι → α → β} {xs : Nat → Raw}
    (cd : GFCauchyData L F xs) (i : ι) (n : Nat) (hn : n ≥ cd.N i) :
    F i (L.view (xs n)) = cd.limitAssign i :=
  cd.cauchy i n (cd.N i) hn (Nat.le_refl _)
```
