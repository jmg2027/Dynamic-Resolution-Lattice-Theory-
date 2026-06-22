# Combos 11-50 — long-tail head (3 specimens each)

## #11  Combo \`FORALL, decide, intro, rw\`  (52 theorems)

### \`zmod6Lens_combine_comm\` (E213/Hypervisor/Lens/Instances/ZMod6.lean)
```lean
theorem zmod6Lens_combine_comm :
    ∀ u v : Nat, zmod6Lens.combine u v = zmod6Lens.combine v u := by
  intro u v
  show (u * v) % 6 = (v * u) % 6
  rw [Nat.mul_comm]

/-- Every Raw `r ≠ Raw.a` whose construction passes through
    `Raw.slash a b` inherits view `0`: the R3-failure zero
    absorbs. 
... [trunc]
```

### \`pellFSMmod101_run_period_25\` (E213/Math/Cohomology/Dyadic/ArithFSM/Mod101.lean)
```lean
theorem pellFSMmod101_run_period_25 :
    ∀ k, pellFSMmod101.run (k + 25) = pellFSMmod101.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod101.step (pellFSMmod101.run (k' + 25))
        = pellFSMmod101.step (pellFSMmod101.run k')
    rw [ih]
```

### \`pellFSMmod11_run_period_5\` (E213/Math/Cohomology/Dyadic/ArithFSM/Mod11.lean)
```lean
theorem pellFSMmod11_run_period_5 :
    ∀ k, pellFSMmod11.run (k + 5) = pellFSMmod11.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod11.step (pellFSMmod11.run (k' + 5))
        = pellFSMmod11.step (pellFSMmod11.run k')
    rw [ih]

/-- ★★★★ Pell mod-1
... [trunc]
```


## #12  Combo \`exact\`  (51 theorems)

### \`bezout_left\` (E213/Firmware/Atomicity/FiveHelpers.lean)
```lean
theorem bezout_left {a b : Nat} (ha : 3 ≤ a) :
    2 * a + 3 * b = 2 * (a - 3) + 3 * (b + 2) := by
  have h1 : 2 * (a - 3) = 2 * a - 6 := mul_sub_distrib ha
  have h2 : 3 * (b + 2) = 3 * b + 6 := Nat.mul_add 3 b 2
  have h6 : 6 ≤ 2 * a := Nat.mul_le_mul_left 2 ha
  have step1 : (2 * a - 6) + (3 * b 
... [trunc]
```

### \`Raw\` (E213/Firmware/Raw/Swap.lean)
```lean
def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩
```

### \`Raw\` (E213/Firmware/RawSwap.lean)
```lean
theorem Raw.swap_injective_fn : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective h
```


## #13  Combo \`AND, anon\`  (48 theorems)

### \`cohabit_peano_depth\` (E213/Math/AxiomSystems/CrossTheoryCohabit.lean)
```lean
theorem cohabit_peano_depth (h : Raw.a ≠ Raw.b) :
    peanoLens.view (r h) = 2 ∧ Lens.depth.view (r h) = 1 :=
  ⟨peano_view h, depth_view h⟩
```

### \`cupAW_bilinear_capstone\` (E213/Math/Cohomology/CupAW/Bilinear.lean)
```lean
theorem cupAW_bilinear_capstone (n a b : Nat)
    (α α' : Cochain n a) (β β' : Cochain n b)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b (Cochain.add α α') β τ_idx
      = xor (cupAW n a b α β τ_idx) (cupAW n a b α' β τ_idx)
    ∧ cupAW n a b α (Cochain.add β β') τ_idx
      = xor (cupA
... [trunc]
```

### \`pell_discriminant_legendre_table\` (E213/Math/Cohomology/Dyadic/Legendre/Small.lean)
```lean
theorem pell_discriminant_legendre_table :
    legendre213 5 3 (by decide) = ⟨2, by decide⟩
    ∧ legendre213 5 5 (by decide) = ⟨0, by decide⟩
    ∧ legendre213 5 7 (by decide) = ⟨2, by decide⟩
    ∧ legendre213 5 11 (by decide) = ⟨1, by decide⟩ :=
  ⟨legendre_5_mod_3, legendre_5_mod_5, legendre_5_m
... [trunc]
```


## #14  Combo \`FORALL\`  (43 theorems)

### \`getBase_eq\` (E213/Firmware/Atomicity/ArityForcingGeneral.lean)
```lean
theorem getBase_eq {N k : Nat} :
    ∀ (x : RawNk N k) (h : isBase x = true), x = .object (getBase x h)
  | .object _, _ => rfl
  | .rel _,    h => by cases h
```

### \`Lens\` (E213/Hypervisor/Lens/Foundations/Initiality.lean)
```lean
theorem Lens.view_unique {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (f : Raw → α)
    (ha : f Raw.a = L.base_a)
    (hb : f Raw.b = L.base_b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = L.combine (f x) (f y)) :
    ∀ r : Raw, f 
... [trunc]
```

### \`parity_succ\` (E213/Kernel/Tactic/Mod213.lean)
```lean
theorem parity_succ : ∀ n, parity (n + 1) = !parity n
  | 0     => rfl
  | 1     => rfl
  | n + 2 => parity_succ n
```


## #15  Combo \`FORALL, intro, rw\`  (42 theorems)

### \`swapLens_view_involutive\` (E213/Hypervisor/Lens/Instances/Swap.lean)
```lean
theorem swapLens_view_involutive :
    ∀ r : Raw, swapLens.view (swapLens.view r) = r := by
  intro r
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap, Raw.swap_swap]

/-- swapLens has an injective view (since it is involutive). -/
```

### \`prodLens_is_meet\` (E213/Hypervisor/Lens/Lattice/Meet.lean)
```lean
theorem prodLens_is_meet {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (hLsym : ∀ u v, L.combine u v = L.combine v u)
    (hMsym : ∀ u v, M.combine u v = M.combine v u)
    (hNL : N.refines L) (hNM : N.refines M) :
    N.refines (prodLens L M) := by
  intro x y hxy
  show (prodLens L
... [trunc]
```

### \`every_lens_factors_through_idLens\` (E213/Hypervisor/Lens/Universal/Flat.lean)
```lean
theorem every_lens_factors_through_idLens {α : Type} (L : Lens α) :
    ∀ r : Raw, L.view r = L.view (idLens.view r) := by
  intro r
  rw [idLens_is_id r]

/-- Sharp form: g := L.view, then L.view r = (L.view ∘ idLens.view) r
    pointwise (PURE — funext-free). -/
```


## #16  Combo \`AND, anon, rfl\`  (33 theorems)

### \`Li_H_ratio_bracket\` (E213/Kernel/Cap_PhysicsAtomicIE.lean)
```lean
theorem Li_H_ratio_bracket :
    Nat.ble (39 * IE_H + 1) (100 * IE_Li) = true ∧
    Nat.ble (100 * IE_Li + 1) (40 * IE_H) = true := ⟨rfl, rfl⟩

/-- 0.68 < IE(Be)/IE(H) < 0.70. -/
```

### \`mpi_sq_bracket\` (E213/Kernel/Cap_PhysicsBrackets.lean)
```lean
theorem mpi_sq_bracket :
    Nat.ble (18001) 18934 = true ∧ Nat.ble (18935) 19500 = true :=
  ⟨rfl, rfl⟩

/-- m_ρ² ≈ 611680, bracket [600000, 620000]. -/
```

### \`cdf_W_in_bracket\` (E213/Kernel/Cap_PhysicsFalsifiers.lean)
```lean
theorem cdf_W_in_bracket :
    Nat.ble 7501 7707 = true ∧ Nat.ble 7708 7800 = true := ⟨rfl, rfl⟩

/-- λ_Cabibbo > 0.225 (5/22 vs 0.225 → 5·1000 > 22·22 = 484). -/
```


## #17  Combo \`AND, FORALL, anon\`  (33 theorems)

### \`cohomology_213_marathon\` (E213/Math/Cohomology/Capstone.lean)
```lean
theorem cohomology_213_marathon :
    -- CA: cochain complex on Δ⁴, δ²=0 sample
    (∀ i : Fin (binom 5 3), delta (delta vertex0_n5) i = false)
    -- CB: ⋆⋆ = id sample
    ∧ (∀ i : Fin (binom 5 1),
         hodgeStar 5 4 1 (hodgeStar 5 1 4 v0_5) i = v0_5 i)
    -- CC: Δ⁴ contractibility witness
  
... [trunc]
```

### \`phase_CD_cup_smoke\` (E213/Math/Cohomology/Cup/Core.lean)
```lean
theorem phase_CD_cup_smoke :
    (∀ i : Fin (binom 5 2),
       cup 5 1 1 (Cochain.zero 5 1) v0_5 i = false)
    ∧ (∀ i : Fin (binom 5 2),
         cup 5 1 1 v0_5 (Cochain.zero 5 1) i = false)
    ∧ (cup 5 1 1 all_true_5_1 all_true_5_1 ⟨0, by decide⟩ = true) :=
  ⟨cup_zero_left_5_1_1, cup_zero_right
... [trunc]
```

### \`phase_CD_leibniz_capstone\` (E213/Math/Cohomology/Cup/Leibniz.lean)
```lean
theorem phase_CD_leibniz_capstone :
    (∀ i : Fin (binom 5 3),
       delta (cup 5 1 1 v0_5 v0_5) i
         = xor (cup 5 2 1 (delta v0_5) v0_5 i)
               (cup 5 1 2 v0_5 (delta v0_5) i))
    ∧ (∀ i : Fin (binom 5 3),
         delta (cup 5 1 1 all_true_5_1 v0_5) i
           = xor (cup 5 2 1
... [trunc]
```


## #18  Combo \`FORALL, IMPLIES\`  (30 theorems)

### \`Tree\` (E213/Firmware/Raw/Cmp.lean)
```lean
theorem Tree.cmp_eq_iff (x y : Tree) : Tree.cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | a => cases y <;> simp [Tree.cmp]
  | b => cases y <;> simp [Tree.cmp]
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => simp [Tree.cmp]
      | b => simp [Tree.cmp]
      | slash x₂
... [trunc]
```

### \`RawBy_bijection\` (E213/Firmware/Raw/CmpIndependence.lean)
```lean
theorem RawBy_bijection (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    ∀ (r : RawBy cmp2),
        transportRawBy cmp1 cmp2 h1 h2
          (transportRawBy cmp2 cmp1 h2 h1 r) = r :=
  transportRawBy_roundtrip cmp1 cmp2 h1 h2
```

### \`Raw\` (E213/Firmware/Raw/Hom.lean)
```lean
theorem Raw.fold_swap_hom {α : Type}
    (ba bb : α) (c : α → α → α) (conj : α → α)
    (h_ba : conj ba = bb) (h_bb : conj bb = ba)
    (h_dist : ∀ u v, conj (c u v) = c (conj u) (conj v))
    (h_comm : ∀ u v, c u v = c v u) (r : Raw) :
    Raw.fold ba bb c (Raw.swap r) = conj (Raw.fold ba bb c r) :
... [trunc]
```


## #19  Combo \`rfl, rw\`  (27 theorems)

### \`canonicalBy_Tree_cmp\` (E213/Firmware/Raw/CmpIndependence.lean)
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

/-- Therefore the underlying predicate of RawBy Tree.cmp = Tree.canoni
... [trunc]
```

### \`composite_a\` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)
```lean
theorem composite_a : composite Raw.a = constTrueLens := by
  unfold composite
  rw [@universalMorphism_a Bool boolXorHasDistinguishing]
  rfl
```

### \`lensUniversalMorphism_factors_level2\` (E213/Hypervisor/Lens/Compose/OnLensImageLevel2.lean)
```lean
theorem lensUniversalMorphism_factors_level2
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    @universalMorphism (Lens (Lens α))
      (lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α)) r =
      constComposite2 α r := by
  have step1 := lensUniversalMorphism_factors_generic (Le
... [trunc]
```


## #20  Combo \`exact, rfl, rw\`  (23 theorems)

### \`fin3_image_in_01\` (E213/Hypervisor/Lens/Instances/Reach.lean)
```lean
theorem fin3_image_in_01 (r : Raw) :
    universalMorphism (Fin 3) r = 0 ∨ universalMorphism (Fin 3) r = 1 := by
  induction r using Raw.rec with
  | a => left; exact universalMorphism_a (Fin 3)
  | b => right; exact universalMorphism_b (Fin 3)
  | slash x y h _ _ =>
      left
      rw [universalMo
... [trunc]
```

### \`wallis_monotonic\` (E213/Math/Cauchy/WallisSeq.lean)
```lean
theorem wallis_monotonic (n : Nat) :
    wallisNum n * wallisDen (n + 1) < wallisNum (n + 1) * wallisDen n := by
  show wallisNum n * (wallisDen n * ((2 * n + 1) * (2 * n + 3)))
       < wallisNum n * (4 * (n + 1) * (n + 1)) * wallisDen n
  have hkk_strict : (2 * n + 1) * (2 * n + 3) < 4 * (n + 1) *
... [trunc]
```

### \`mod3_three_mul\` (E213/Math/ModArith/PureNatMod3.lean)
```lean
theorem mod3_three_mul (k : Nat) : mod3 (3 * k) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show mod3 (3 * (n + 1)) = 0
      rw [Nat.mul_succ]
      show mod3 (3 * n + 3) = 0
      exact ih
```


## #21  Combo \`IMPLIES, rw\`  (21 theorems)

### \`slashTree_canonical_input\` (E213/Firmware/Raw/CmpIndependence.lean)
```lean
theorem slashTree_canonical_input {cmp : Tree → Tree → Ordering}
    (h : CmpProps cmp) (s u : Tree) (hsu : cmp s u = .lt) :
    slashTree cmp s u = .slash s u := by
  unfold slashTree; rw [hsu]

/-- slashTree of {a, b} = canonical .slash result. -/
```

### \`R4_conj_agrees_on_image\` (E213/Hypervisor/Lens/Characterisation/Core.lean)
```lean
theorem R4_conj_agrees_on_image
    {α : Type} {L : Hypervisor.Lens α} {conj1 conj2 : α → α}
    (h1 : SwapMatching L conj1) (h2 : SwapMatching L conj2)
    (r : Raw) : conj1 (L.view r) = conj2 (L.view r) := by
  have e1 := h1.2.2 r
  have e2 := h2.2.2 r
  rw [← e1, ← e2]

/-- **R4 uniqueness on sur
... [trunc]
```

### \`product_bits_eq\` (E213/Math/Cohomology/Dyadic/ProductFSMRun.lean)
```lean
theorem product_bits_eq {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool) (k : Nat) :
    (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product hm f1 f2 g).bits k = g (f1.bits k) (f2.bits k) := by
  show (E213.Math.Cohomology.Dyadic.ProductFSM.BitFSM.product hm f
... [trunc]
```


## #22  Combo \`anon\`  (19 theorems)

### \`Raw\` (E213/Firmware/Raw/SwapSlashInjective.lean)
```lean
theorem Raw.swap_injective' : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective h

/-- `Function.Surjective` form (self-inverse). -/
```

### \`Raw\` (E213/Firmware/RawSwap.lean)
```lean
theorem Raw.swap_injective_fn : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective h
```

### \`iffEquiv_refl\` (E213/Hypervisor/Lens/AxiomLenses/Core/Propext.lean)
```lean
theorem iffEquiv_refl (P : Prop) : iffEquiv P P :=
  ⟨id, id⟩
```


## #23  Combo \`exact, intro, rw\`  (19 theorems)

### \`idLens_injective\` (E213/Hypervisor/Lens/Instances/Identity.lean)
```lean
theorem idLens_injective : Function.Injective idLens.view := by
  intro x y hxy
  rw [idLens_is_id x, idLens_is_id y] at hxy
  exact hxy

/-- **Yoneda-dual**: Raw element r as a function that evaluates
    every Lens α.  The dual perspective of `L.view : Raw → α`. -/
```

### \`swapLens_injective\` (E213/Hypervisor/Lens/Instances/Swap.lean)
```lean
theorem swapLens_injective : Function.Injective swapLens.view := by
  intro x y hxy
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap] at hxy
  exact Raw.swap_injective hxy
```

### \`depth_refines_tierLens\` (E213/Hypervisor/Lens/Leaves/DepthJoin.lean)
```lean
theorem depth_refines_tierLens : Lens.depth.refines tierLens := by
  intro r r' h
  show tierLens.view r = tierLens.view r'
  rw [tierLens_view_eq_tier, tierLens_view_eq_tier]
  exact tier_eq_of_depth_eq r r' h

/-- **tierLens.view takes exactly 3 values** (all of 0, 1, 2 are hit). -/
```


## #24  Combo \`decide, simp\`  (19 theorems)

### \`cohom_class_count_pow\` (E213/Math/Cohomology/HodgeConjecture/Bridge/CohomologyWithoutQuotient.lean)
```lean
theorem cohom_class_count_pow : num_cohom_classes_K5_2 = 2 ^ 6 := by decide
```

### \`euler_via_betti\` (E213/Math/Cohomology/HodgeConjecture/Bridge/DiscreteGeometry.lean)
```lean
theorem euler_via_betti : (1 : Nat) + 4 = 5 := by decide
```

### \`routeSum_galois_eq_fixed\` (E213/Math/Cohomology/HodgeConjecture/Bridge/PhaseRouting.lean)
```lean
theorem routeSum_galois_eq_fixed : routeSum routeGalois 5 = fixedCount := by decide
```


## #25  Combo \`FORALL, intro, rfl, rw\`  (17 theorems)

### \`Tree\` (E213/Firmware/Raw/Levels.lean)
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
      have
... [trunc]
```

### \`idLens_is_id\` (E213/Hypervisor/Lens/Instances/Identity.lean)
```lean
theorem idLens_is_id : ∀ r : Raw, idLens.view r = r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : idLens.view (Raw.slash x y h)
                   = idLens.combine (idLens.view x) (idLens.view y) :=
        Raw.fold_slash idLen
... [trunc]
```

### \`swapLens_view_eq_swap\` (E213/Hypervisor/Lens/Instances/Swap.lean)
```lean
theorem swapLens_view_eq_swap : ∀ r : Raw, swapLens.view r = Raw.swap r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : swapLens.view (Raw.slash x y h)
                   = swapLens.combine (swapLens.view x) (swapLens.view y) :=

... [trunc]
```


## #26  Combo \`AND, decide, match\`  (17 theorems)

### \`b1_reduction\` (E213/Math/Cohomology/Bipartite/Filled.lean)
```lean
theorem b1_reduction :
    -- 0 cells filled: b_1 = 8 (current Bipartite32 framework)
    (12 - 5 + 1 = 8)
    -- 1 cell filled: b_1 = 7
    ∧ (12 - 5 + 1 - 1 = 7)
    -- 2 cells filled: b_1 = 6
    ∧ (12 - 5 + 1 - 2 = 6)
    -- 3 cells (all): b_1 = 5
    ∧ (12 - 5 + 1 - 3 = 5) := by decide

/-- b_1
... [trunc]
```

### \`b1_eq_8_dim_count\` (E213/Math/Cohomology/Bipartite/V32Betti.lean)
```lean
theorem b1_eq_8_dim_count :
    -- |im δ₀| · |H¹| = |C¹|
    16 * 256 = 4096
    -- |H¹| = 2^8
    ∧ 256 = 2^8
    -- |im δ₀| · |ker δ₀| = |C⁰|
    ∧ 16 * 2 = 32 := by decide

/-- Cross-link: b₁ = NS² − 1 = 8 (matches PhotonKernel.b_1_eq_8). -/
```

### \`diamond_audit_no_free_parameters\` (E213/Math/Cohomology/DiamondAudit.lean)
```lean
theorem diamond_audit_no_free_parameters :
    NS * NT = 6
    ∧ NS * NS - 1 = 8
    ∧ d * d = 25
    ∧ (NS + NT) * (NS + NT) = 25
    ∧ 12 * NT * 5 / 4 = 30
    ∧ E213.Physics.AlphaEM.Prefactors.c_lat * NS * NT = 12 := by decide

/-- ★ Falsifier coupling: any wrong prediction → atomic mismatch
    
... [trunc]
```


## #27  Combo \`anon, rfl\`  (15 theorems)

### \`atomic_five\` (E213/Firmware/Atomicity/Five.lean)
```lean
theorem atomic_five : Atomic 5 :=
  ⟨1, 1, rfl, ⟨rfl, rfl⟩, fun a b h => solve_2a_3b_eq_5 a b h.symm⟩
```

### \`cauchyEquiv_refl\` (E213/Math/AxiomSystems/ClassicalAnalysisCompletenessAsLens.lean)
```lean
theorem cauchyEquiv_refl (s : CauchySeq) : cauchyEquiv s s :=
  fun _ => ⟨0, fun _ _ => rfl⟩

/-- The completeness lens — collapses cauchyEquiv-related sequences
    into the same "real number."  Applying this lens requires
    Quot.sound (to identify equivalence classes with values) +
    funext (t
... [trunc]
```

### \`I_mul_J\` (E213/Math/CayleyDickson/CDDouble.lean)
```lean
theorem I_mul_J : I' * J = ⟨0, ZI.I⟩ := by
  show mul I' J = ⟨0, ZI.I⟩
  unfold mul
  apply ext
  · show ZI.I * 0 - (⟨1, 0⟩ : ZI).conj * 0 = 0
    apply ZI.ext
    · show _ = (0 : Int); rfl
    · show _ = (0 : Int); rfl
  · show (⟨1, 0⟩ : ZI) * ZI.I + 0 * ZI.I.conj = ZI.I
    apply ZI.ext
    · show
... [trunc]
```


## #28  Combo \`cases, rfl\`  (15 theorems)

### \`Ordering_swap_swap\` (E213/Firmware/Raw/CmpIndependence.lean)
```lean
theorem Ordering_swap_swap (o : Ordering) : o.swap.swap = o := by
  cases o <;> rfl

/-- cmpRev also satisfies CmpProps (involutive). -/
```

### \`lensXor_comm\` (E213/Hypervisor/Lens/Compose/OnLens.lean)
```lean
theorem lensXor_comm (L M : Lens Bool) : lensXor L M = lensXor M L := by
  unfold lensXor
  -- Structural equality on Lens record.
  congr 1
  · cases L.base_a <;> cases M.base_a <;> rfl
  · cases L.base_b <;> cases M.base_b <;> rfl
  · funext x y
    cases L.combine x y <;> cases M.combine x y <;> 
... [trunc]
```

### \`negSqLens_sq\` (E213/Hypervisor/Lens/Instances/NegSq.lean)
```lean
theorem negSqLens_sq (v : Bool) : sq negSqLens v = !v := by
  cases v <;> rfl

/-- negSqLens is not Idempotent (sq v = !v ≠ v). -/
```


## #29  Combo \`NEG, decide\`  (15 theorems)

### \`squeeze_Nat_via_trichotomy\` (E213/Math/Cohomology/HodgeConjecture/Bridge/G9ReductioVoid.lean)
```lean
theorem squeeze_Nat_via_trichotomy (n m : Nat)
    (h1 : ¬(n < m)) (h2 : ¬(m < n)) : n = m :=
  squeeze_via_trichotomy n m h1 h2 (Nat.lt_trichotomy n m)
```

### \`eleven_not_in\` (E213/Physics/Atomic/Complete1.lean)
```lean
theorem eleven_not_in : ¬ ((11 : Nat) ∈ atomic_1_complete) := by decide
```

### \`eleven_not_in_sample\` (E213/Physics/Atomic/Enumeration.lean)
```lean
theorem eleven_not_in_sample : ¬ ((11 : Nat) ∈ atomic_1_sample) := by decide

/-- Random non-atomic 17 ∉ Atomic-1 sample. -/
```


## #30  Combo \`decide, exact\`  (14 theorems)

### \`eulerNum_pos\` (E213/Math/Cauchy/EulerSeq.lean)
```lean
theorem eulerNum_pos (_n : Nat) : 1 ≤ eulerNum _n := by
  induction _n with
  | zero => decide
  | succ k _ih =>
      show 1 ≤ (k + 1) * eulerNum k + 1
      exact Nat.le_add_left 1 _
```

### \`pellX_pos\` (E213/Math/Cauchy/PellSeq.lean)
```lean
theorem pellX_pos (n : Nat) : 1 ≤ pellX n := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 1 ≤ 3 * (pellPair k).1 + 4 * (pellPair k).2
      have hxk : 1 ≤ (pellPair k).1 := ih
      have h3 : 3 ≤ 3 * (pellPair k).1 := by
        have := Nat.mul_le_mul_left 3 hxk
        rwa [
... [trunc]
```

### \`wallisNum_pos\` (E213/Math/Cauchy/WallisSeq.lean)
```lean
theorem wallisNum_pos (n : Nat) : 1 ≤ wallisNum n := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 1 ≤ wallisNum k * (4 * (k + 1) * (k + 1))
      have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h1 : 1 ≤ 4 * (k + 1) :=
        Nat.le_trans (by decide : (1 :
... [trunc]
```


## #31  Combo \`FORALL, IMPLIES, decide\`  (14 theorems)

### \`tribFSMmod2_signature_period_4_from_1\` (E213/Math/Cohomology/Dyadic/ArithFSM/V3.lean)
```lean
theorem tribFSMmod2_signature_period_4_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod2.bits 4 1 tribFSMmod2_bits_period_4 (by decide)
```

### \`fibFSMmod11_signature_period_10_from_1\` (E213/Math/Cohomology/Dyadic/Fib/FSMmod11.lean)
```lean
theorem fibFSMmod11_signature_period_10_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod11.bits (k + 10)
        = signature fibFSMmod11.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod11.bits 10 1 fibFSMmod11_bits_period_10 (by decide)
```

### \`fibFSMmod13_signature_period_28_from_1\` (E213/Math/Cohomology/Dyadic/Fib/FSMmod13.lean)
```lean
theorem fibFSMmod13_signature_period_28_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod13.bits (k + 28) = signature fibFSMmod13.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod13.bits 28 1 fibFSMmod13_bits_period_28 (by decide)
```


## #32  Combo \`FORALL, exact, intro\`  (13 theorems)

### \`joinEquiv_parityLens_boolXorLens_universal\` (E213/Hypervisor/Lens/Instances/ParityXorJoin.lean)
```lean
theorem joinEquiv_parityLens_boolXorLens_universal :
    ∀ r r' : Raw, JoinEquiv parityLens boolXorLens r r' := by
  intro r r'
  exact JoinEquiv.trans (join_to_a r) (JoinEquiv.symm (join_to_a r'))

/-- **Consequence**: any symmetric-combine Lens refining both
    parityLens and boolXorLens is const
... [trunc]
```

### \`swap_invariant_equates_orbit\` (E213/Hypervisor/Lens/Kernel/SwapInvariant.lean)
```lean
theorem swap_invariant_equates_orbit {α : Type} (L : Lens α)
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    ∀ r : Raw, L.equiv r (Raw.swap r) := by
  intro r
  show L.view r = L.view (Raw.swap r)
  exact (hinv r).symm

/-- A swap-invariant Lens has a swap-invariant kernel:
    r ~ r' ↔
... [trunc]
```

### \`joinLens_is_least\` (E213/Hypervisor/Lens/Lattice/Join.lean)
```lean
theorem joinLens_is_least {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLN : L.refines N) (hMN : M.refines N) :
    (joinLens L M).refines N := by
  intro r r' h
  have hJE : JoinEquiv L M r r' := (joinLens_kernel L M r r').mp h
  
... [trunc]
```


## #33  Combo \`AND, anon, decide\`  (13 theorems)

### \`diamond_b1\` (E213/Math/Cohomology/DiamondShape.lean)
```lean
theorem diamond_b1 :
    E213.Physics.Couplings.PhotonKernel.b_1 = 8
    ∧ (8 : Nat) = NS * NS - 1 :=
  ⟨E213.Physics.Couplings.PhotonKernel.b_1_eq_8, by decide⟩

/-- ★★★ DIAMOND CRYSTAL CAPSTONE ★★★ -/
```

### \`signature_atomicity_capstone\` (E213/Math/Cohomology/Dyadic/AtomicityConnection.lean)
```lean
theorem signature_atomicity_capstone :
    E213.Physics.Simplex.Counts.NS = 3 ∧ E213.Physics.Simplex.Counts.NT = 2
    ∧ E213.Physics.Simplex.Counts.d = 5 ∧ E213.Physics.Simplex.Counts.NS + E213.Physics.Simplex.Counts.NT
        = E213.Physics.Simplex.Counts.d :=
  ⟨signature_S_count, signature_T_co
... [trunc]
```

### \`walk_smoke\` (E213/Math/Cohomology/Dyadic/Conjecture.lean)
```lean
theorem walk_smoke :
    validWalk [⟨0, by decide⟩, ⟨4, by decide⟩] = true
    ∧ validWalk [⟨0, by decide⟩, ⟨11, by decide⟩] = false :=
  ⟨by decide, by decide⟩

/-- 1/3 period [F, T] realised as walk [0, 5]: T_0 shared. -/
```


## #34  Combo \`decide, match\`  (12 theorems)

### \`cupAW_v0_v0_off_diagonal\` (E213/Math/Cohomology/CupAW/Core.lean)
```lean
theorem cupAW_v0_v0_off_diagonal :
    cupAW 5 1 1 v0_5 v0_5 ⟨1, by decide⟩ = false := by decide

/-- ★ AW cup product smoke capstone — well-defined and matches
    overlap convention at the diagonal. -/
```

### \`legendre_8_mod_7\` (E213/Math/Cohomology/Dyadic/Pell/ProperBridge.lean)
```lean
theorem legendre_8_mod_7 :
    legendre213 8 7 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★ pisano_predict_proper matches TIGHT Pell proper periods. -/
```

### \`fractal_edge_atomic\` (E213/Math/Cohomology/Fractal/AlphaGUT.lean)
```lean
theorem fractal_edge_atomic :
    E213.Math.Cohomology.Fractal.V25.numE = 2 * 3 * 2 * 5 * 5 := by decide

/-- ★ Bridge: α_GUT structural identification.
      6  = b_1(K_5)           = numerator
      25 = numV(K_{25})        = denominator integer
      π² = ζ(2) · 6            = standard transcende
... [trunc]
```


## #35  Combo \`AND, FORALL, IMPLIES, anon\`  (12 theorems)

### \`number_theory_213_capstone\` (E213/Math/Cohomology/Dyadic/NumberTheory213.lean)
```lean
theorem number_theory_213_capstone :
    -- Step 1: CRT multiplicativity (LCM stream closure)
    (∀ (bs1 bs2 : Nat → Bool) (p q : Nat),
      0 < p → 0 < q →
      (∀ k, bs1 (k + p) = bs1 k) → (∀ k, bs2 (k + q) = bs2 k) →
      ∀ (g : Bool → Bool → Bool) k,
        g (bs1 (k + Nat.lcm p q)) (bs2 (k
... [trunc]
```

### \`trib_crt_4_capstone\` (E213/Math/Cohomology/Dyadic/Trib/CRT4Capstone.lean)
```lean
theorem trib_crt_4_capstone :
    -- Previous 3-modulus capstone
    ((∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k)
     ∧ (∀ k, k ≥ 1 →
         signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k)
     ∧ (∀ k, tribFSMmod3.bits (k + 13) = tribFSMmod3.bits k)
     ∧ (∀ k, k ≥ 1 
... [trunc]
```

### \`trib_crt_capstone\` (E213/Math/Cohomology/Dyadic/Trib/CRTCapstone.lean)
```lean
theorem trib_crt_capstone :
    -- mod 2 bits
    (∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k)
    -- mod 2 sig (from step 1)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k)
    -- mod 3 bits
    ∧ (∀ k, tribFSMmod3.bits (k + 13) = tribFSMmod3.b
... [trunc]
```


## #36  Combo \`cases, rfl, rw\`  (11 theorems)

### \`Tree\` (E213/Firmware/Raw/Cmp.lean)
```lean
theorem Tree.cmp_eq_iff (x y : Tree) : Tree.cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | a => cases y <;> simp [Tree.cmp]
  | b => cases y <;> simp [Tree.cmp]
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => simp [Tree.cmp]
      | b => simp [Tree.cmp]
      | slash x₂
... [trunc]
```

### \`Raw\` (E213/Firmware/Raw/Slash.lean)
```lean
def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            unfold Tree.canonical
            rw [x.property, y.property, hc]; rfl⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
       
... [trunc]
```

### \`Tree\` (E213/Firmware/Raw/Swap.lean)
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


## #37  Combo \`decide, exact, rw\`  (11 theorems)

### \`int_image_nonneg\` (E213/Hypervisor/Lens/Instances/Reach.lean)
```lean
theorem int_image_nonneg (r : Raw) : 0 ≤ universalMorphism Int r := by
  induction r using Raw.rec with
  | a =>
      rw [universalMorphism_a Int]
      exact Int.le_refl 0
  | b =>
      rw [universalMorphism_b Int]
      decide
  | slash x y h ihx ihy =>
      rw [universalMorphism_slash Int x y 
... [trunc]
```

### \`euler_lower_step\` (E213/Math/Cauchy/EulerGenericPure.lean)
```lean
theorem euler_lower_step (j b k : Nat) (hb : b ≥ 1)
    (h_inv : b * eulerNum k ≥ j * eulerDen k + 1) :
    b * eulerNum (k + 1) ≥ j * eulerDen (k + 1) + 1 := by
  show b * ((k + 1) * eulerNum k + 1) ≥ j * ((k + 1) * eulerDen k) + 1
  -- LHS = (k+1) * (b * eulerNum k) + b
  -- RHS = (k+1) * (j * eul
... [trunc]
```

### \`euler_orderProj_above_3\` (E213/Math/Cauchy/EulerSeq.lean)
```lean
theorem euler_orderProj_above_3 (m k : Nat) (h3km : 3 * k ≤ m) (n : Nat) :
    orderProj m k (abLens.view (eulerRaw n).val) = true := by
  rw [eulerRaw_view]
  show decide (eulerNum n * k ≤ eulerDen n * m) = true
  have hu := euler_upper_inv n
  have h1 : eulerNum n * k ≤ 3 * eulerDen n * k :=
    N
... [trunc]
```


## #38  Combo \`intro, rw\`  (11 theorems)

### \`all_refine_constLens\` (E213/Hypervisor/Lens/Lattice/Lattice.lean)
```lean
theorem all_refine_constLens {α : Type} (e : α) (L : Lens α) :
    L.refines (constLens e) := by
  intro x y _
  show (constLens e).view x = (constLens e).view y
  rw [constLens_view, constLens_view]
```

### \`leaves_refines_parity\` (E213/Hypervisor/Lens/Leaves/RefinesParity.lean)
```lean
theorem leaves_refines_parity : Lens.leaves.refines parityLens := by
  intro x y hxy
  have hxy' : Lens.leaves.view x = Lens.leaves.view y := hxy
  show parityLens.view x = parityLens.view y
  rw [parityLens_view_eq_leaves_odd x, parityLens_view_eq_leaves_odd y, hxy']
```

### \`idLens_is_bottom\` (E213/Hypervisor/Lens/Universal/Flat.lean)
```lean
theorem idLens_is_bottom {α : Type} (L : Lens α) :
    idLens.refines L := by
  intro r r' h
  show L.view r = L.view r'
  have hview : idLens.view r = idLens.view r' := h
  rw [idLens_is_id r, idLens_is_id r'] at hview
  rw [hview]
```


## #39  Combo \`cases\`  (11 theorems)

### \`ext\` (E213/Math/CayleyDickson/CDDouble.lean)
```lean
theorem ext {u v : Lipschitz} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- **Conjugation** on `Lipschitz`: flip imaginary, ZI-conj the real. -/
```

### \`ext\` (E213/Math/CayleyDickson/Cayley.lean)
```lean
theorem ext {u v : Cayley} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- CD multiplication (same formula as layer 1, lifted). -/
```

### \`ext\` (E213/Math/CayleyDickson/Pathion.lean)
```lean
theorem ext {u v : Pathion} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr
```


## #40  Combo \`exact, intro\`  (10 theorems)

### \`const_lenses_distinct\` (E213/Hypervisor/Lens/Compose/OnLens.lean)
```lean
theorem const_lenses_distinct : constTrueLens ≠ constFalseLens := by
  intro h
  have h_base_a : constTrueLens.base_a = constFalseLens.base_a :=
    congrArg Lens.base_a h
  exact Bool.noConfusion h_base_a
```

### \`refines_refl\` (E213/Hypervisor/Lens/Refines/Preorder.lean)
```lean
theorem refines_refl {α : Type} (L : Lens α) : L.refines L := by
  intro x y h; exact h

/-- Transitivity. -/
```

### \`true_ne_false\` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)
```lean
theorem true_ne_false : (True : Prop) ≠ False := by
  intro h; exact h.mp trivial

/-- **Prop as an object of the distinguishing-framework category**.
    `True ≠ False` + `propXor` (= boolean parallel of Raw.slash). -/
```


## #41  Combo \`NEG, exact, intro\`  (10 theorems)

### \`leaves_not_refines_abLens\` (E213/Hypervisor/Lens/Instances/AB.lean)
```lean
theorem leaves_not_refines_abLens : ¬ Lens.leaves.refines abLens := by
  intro h
  exact abLens_distinguishes (h rAAB rABB leaves_equates)
```

### \`parity_not_refines_xor\` (E213/Hypervisor/Lens/Instances/ParityXorIncomparable.lean)
```lean
theorem parity_not_refines_xor : ¬ parityLens.refines boolXorLens := by
  intro h
  exact xor_distinguishes_ab (h Raw.a Raw.b parity_equates_ab)

/-- Witness `a / (a / (a/b))` — a-count=3 odd, total-count=4 even. -/
```

### \`leaves_not_refines_depth\` (E213/Hypervisor/Lens/Leaves/DepthIncomparable.lean)
```lean
theorem leaves_not_refines_depth : ¬ Lens.leaves.refines Lens.depth := by
  intro h
  exact depth_distinguishes (h rDeep rBalanced leaves_equates)
```


## #42  Combo \`EXISTS, anon\`  (10 theorems)

### \`image_contains_a\` (E213/Hypervisor/Lens/Instances/Reach.lean)
```lean
theorem image_contains_a (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.a :=
  ⟨Raw.a, universalMorphism_a α⟩

/-- The image always contains d.b. -/
```

### \`abLens_surjective\` (E213/Math/Cauchy/PellSeq.lean)
```lean
theorem abLens_surjective (s a b : Nat) (hsum : a + b = s) (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ∃ r : Raw, abLens.view r = (a, b) :=
  let ⟨r, hr⟩ := abLens_witness s a b hsum ha hb
  ⟨r, hr⟩
```

### \`not_alternative\` (E213/Math/CayleyDickson/Sedenion.lean)
```lean
theorem not_alternative :
    ∃ a b : Sedenion, (a * a) * b ≠ a * (a * b) :=
  ⟨zd_left, zd_right, alt_fails_at_zd⟩
```


## #43  Combo \`AND\`  (10 theorems)

### \`canonicalAndMap_slash\` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)
```lean
theorem canonicalAndMap_slash (x y : Raw) (h : x ≠ y) :
    canonicalAndMap (Raw.slash x y h)
      = (canonicalAndMap x ∧ canonicalAndMap y) :=
  @universalMorphism_slash Prop propAsDistinguishingAnd x y h

/-- Or-based Prop instance — dual to And. -/
```

### \`two_pow_sum_inj_full\` (E213/Meta/BitPatternUniqueness.lean)
```lean
theorem two_pow_sum_inj_full
    (m n p q : Nat) (hmn : m ≠ n)
    (heq : 2^m + 2^n = 2^p + 2^q) :
    (m = p ∧ n = q) ∨ (m = q ∧ n = p) :=
  two_pow_sum_inj_unordered m n p q hmn
    (two_pow_sum_distinct_forces_distinct m n p q hmn heq) heq
```

### \`zeta2_bracket\` (E213/Physics/Couplings/AlphaGUTPhase3Derivation.lean)
```lean
theorem zeta2_bracket : S 3 = (49, 36) ∧ upper 3 = (183, 108) :=
  bracket_endpoints_3

/-- 1/α_GUT lower at N=3: d²·S(3) = 25·49/36 = 1225/36. -/
```


## #44  Combo \`anon, decide\`  (10 theorems)

### \`K_mul_I\` (E213/Math/CayleyDickson/CDDouble.lean)
```lean
theorem K_mul_I : (I' * J) * I' = J := by decide

/-- `j · i = -k`.  (Distinct from `J_mul_I` above which shows
    the same product = `⟨0, negI⟩` directly.) -/
```

### \`encode_bijection\` (E213/Math/Cohomology/EncodingBijection.lean)
```lean
theorem encode_bijection (σ : Cochain 5 1) (j : Fin 5) :
    σ j = cochainAt 5 1 (encode_5_1 σ) j :=
  let h_pw : σ j = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                           (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                           (σ ⟨4, by decide⟩) j :=
    E213.Math.Coho
... [trunc]
```

### \`encode_bijection\` (E213/Math/Cohomology/EncodingBijection52.lean)
```lean
theorem encode_bijection (σ : Cochain 5 2) (j : Fin 10) :
    σ j = cochainAt 5 2 (encode_5_2 σ) j :=
  let h_pw : σ j = pattern
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
      (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
      (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (
... [trunc]
```


## #45  Combo \`IMPLIES, cases, rfl\`  (10 theorems)

### \`cutMax_idempotent_at\` (E213/Math/Real213/CutAlgebraic.lean)
```lean
theorem cutMax_idempotent_at (c : Nat → Nat → Bool) (m k : Nat) :
    cutMax c c m k = c m k := by
  show (c m k && c m k) = c m k
  cases c m k <;> rfl

/-- cutMax idempotent: max(c, c) ≡ c (cutEq, PURE). -/
```

### \`cutMin_comm_at\` (E213/Math/Real213/CutMaxMin.lean)
```lean
theorem cutMin_comm_at (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutMin cx cy m k = cutMin cy cx m k := by
  show (cx m k || cy m k) = (cy m k || cx m k)
  cases cx m k <;> cases cy m k <;> rfl
```


## #46  Combo \`FORALL, IMPLIES, intro, rw\`  (9 theorems)

### \`refines_of_factor\` (E213/Hypervisor/Lens/Compose/Factoring.lean)
```lean
theorem refines_of_factor {α β : Type} (L : Lens α) (M : Lens β)
    (g : α → β) (hfactor : ∀ r : Raw, M.view r = g (L.view r)) :
    L.refines M := by
  intro x y hxy
  have hxy' : L.view x = L.view y := hxy
  show M.view x = M.view y
  rw [hfactor x, hfactor y, hxy']
```

### \`refines_of_morphism\` (E213/Hypervisor/Lens/Compose/Morphism.lean)
```lean
theorem refines_of_morphism {α β : Type} (L : Lens α) (M : Lens β)
    (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) : L.refines M := by
  intro x y hxy
  have hx : M.view x = h (L.view x) :
... [trunc]
```

### \`ratio_one_below_cut_eq_diagonal\` (E213/Math/Cauchy/Archimedean.lean)
```lean
theorem ratio_one_below_cut_eq_diagonal (xs ys : Nat → Raw)
    (hx : ∀ n, abLens.view (xs n) = (n + 1, n + 1))
    (hy : ∀ n, abLens.view (ys n) = (n + 1, n + 2))
    (cdx : OrderCauchyData xs) (cdy : OrderCauchyData ys)
    (hcdx : ∀ m k, cdx.cut m k = decide (k ≤ m))
    (hcdy : ∀ m k, cdy.cut m 
... [trunc]
```


## #47  Combo \`decide, refine\`  (9 theorems)

### \`xor_distinguishes_ab\` (E213/Hypervisor/Lens/Instances/ParityXorIncomparable.lean)
```lean
theorem xor_distinguishes_ab :
    boolXorLens.view Raw.a ≠ boolXorLens.view Raw.b := by decide

/-- parityLens does not refine boolXorLens (loses the a,b distinction). -/
```

### \`depth_distinguishes\` (E213/Hypervisor/Lens/Leaves/DepthIncomparable.lean)
```lean
theorem depth_distinguishes :
    Lens.depth.view rDeep ≠ Lens.depth.view rBalanced := by decide

/-- **leaves does not refine depth**. -/
```

### \`leaves_refines_leafLens\` (E213/Hypervisor/Lens/Properties/Leaf.lean)
```lean
theorem leaves_refines_leafLens : Lens.leaves.refines leafLens :=
  refines_of_factor Lens.leaves leafLens
    (fun n => decide (n ≥ 2)) leafLens_view_eq
```


## #48  Combo \`decide, rw\`  (9 theorems)

### \`aPrism_b\` (E213/Hypervisor/Lens/Instances/Prism.lean)
```lean
theorem aPrism_b : aPrism.preview Raw.b = none := by
  unfold aPrism caseElement
  show (if (Raw.b : Raw) = Raw.a then some () else none) = none
  rw [if_neg (by decide)]
```

### \`universalMorphism_commute_iff\` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)
```lean
theorem universalMorphism_commute_iff (r : Raw) :
    @universalMorphism Prop propAsDistinguishingIff r
      = boolToProp (@universalMorphism Bool boolIffHasDistinguishing r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingIff Raw.a = True
... [trunc]
```

### \`nToRawBool_self\` (E213/Math/Infinity/BoolSpace.lean)
```lean
theorem nToRawBool_self (n : Nat) :
    nToRawBool n (rawTower n) = true := by
  show decide (rawTower n = rawTower n) = true
  rw [decide_eq_true_eq]

/-- `nToRawBool n` evaluated at `rawTower m` is `false`
    when `n ≠ m`. -/
```


## #49  Combo \`simp\`  (9 theorems)

### \`conj_conj\` (E213/Math/CayleyDickson/ZI.lean)
```lean
theorem conj_conj (u : ZI) : u.conj.conj = u := by
  apply ext <;> simp [conj]
```

### \`conj_conj\` (E213/Math/CayleyDickson/ZSqrt.lean)
```lean
theorem conj_conj (u : ZSqrt D) : u.conj.conj = u := by
  apply ext <;> simp [conj]
```

### \`conj_conj\` (E213/Math/CayleyDickson/ZSqrt2.lean)
```lean
theorem conj_conj (u : Z2) : u.conj.conj = u := by
  apply ext <;> simp [conj]
```


## #50  Combo \`omega\`  (9 theorems)

### \`add_zero\` (E213/Math/CayleyDickson/ZIArith.lean)
```lean
theorem add_zero (u : ZI) : u + 0 = u := by
  apply ext
  · show u.re + 0 = u.re; omega
  · show u.im + 0 = u.im; omega
```

### \`normSq_nonneg\` (E213/Math/CayleyDickson/ZIDomain.lean)
```lean
theorem normSq_nonneg (u : ZI) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + u.im * u.im
  have h1 := IntHelpers.mul_self_nonneg u.re
  have h2 := IntHelpers.mul_self_nonneg u.im
  omega
```

### \`conj_conj\` (E213/Math/CayleyDickson/ZOmega.lean)
```lean
theorem conj_conj (u : ZOmega) : u.conj.conj = u := by
  apply ext
  · show (u.re - u.im) - (-u.im) = u.re
    omega
  · show -(-u.im) = u.im
    omega
```


## Sample from combos 51-200 (1 specimen each, every 10th)

### Rank 51 (n=9): \`AND, decide, simp\`
  *Specimen: \`b1_filling_table\` from E213/Math/Cohomology/Bipartite/Filled.lean*
```lean
theorem b1_filling_table :
    (8 - 0 = 8)
    ∧ (8 - 1 = 7)
    ∧ (8 - 2 = 6)
    ∧ (8 - 3 = 5)
    ∧ (8 - 4 = 4) := by decide

/-- ★ Phase D capstone — 2-cell filling on K_{3,2}^{(2)}.

    Filling all 3 simple 4-cycles: b_1 drops to 5.
    Open: physical interpretation of "which cells filled". -/
```

### Rank 61 (n=7): \`decide, intro, rw\`
  *Specimen: \`depth_equal\` from E213/Hypervisor/Lens/Properties/ProdBelowId.lean*
```lean
theorem depth_equal : Lens.depth.view rA = Lens.depth.view rB := by decide

private theorem leaves_sym : ∀ u v : Nat, u + v = v + u := Nat.add_comm

private theorem depth_sym :
    ∀ u v : Nat, 1 + max u v = 1 + max v u := by
  intro u v; rw [Nat.max_comm]

/-- prod of (leaves, depth) equates rA and
... [trunc]
```

### Rank 71 (n=6): \`IMPLIES, exact, intro\`
  *Specimen: \`lens_equiv_symm\` from E213/Hypervisor/Lens/Properties/EquivProperties.lean*
```lean
theorem lens_equiv_symm {α : Type} (L : Lens α) (x y : Raw) :
    L.equiv x y → L.equiv y x := by
  intro h; exact h.symm
```

### Rank 81 (n=5): \`FORALL, IMPLIES, cases, exact, intro, rw\`
  *Specimen: \`R3_view_nonVanishing\` from E213/Hypervisor/Lens/Characterisation/Core.lean*
```lean
theorem R3_view_nonVanishing
    {α : Type} [Zero α] (L : Hypervisor.Lens α)
    (hba : L.base_a ≠ 0) (hbb : L.base_b ≠ 0)
    (hcomm : ∀ u v : α, L.combine u v = L.combine v u)
    (hnz : ∀ u v : α, L.combine u v = 0 → u = 0 ∨ v = 0)
    (r : Raw) : L.view r ≠ 0 := by
  induction r using Raw.rec wi
... [trunc]
```

### Rank 91 (n=4): \`cases, match\`
  *Specimen: \`cases_lt_three\` from E213/Kernel/Tactic/Nat213.lean*
```lean
theorem cases_lt_three {n : Nat} (h : n < 3) :
    n = 0 ∨ n = 1 ∨ n = 2 :=
  match Nat.lt_or_ge n 2 with
  | Or.inl hlt => (cases_lt_two hlt).imp id Or.inl
  | Or.inr hge =>
    Or.inr (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h) hge))

/-- `n < 4 → n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3`.  ∅-axiom. -/
```

### Rank 101 (n=4): \`AND, EXISTS, FORALL, IMPLIES, anon, exact, intro, refine, rfl, rw\`
  *Specimen: \`fsm_signature_period_bound\` from E213/Math/Cohomology/Dyadic/BitFSM/Bound.lean*
```lean
theorem fsm_signature_period_bound {n : Nat} (m : BitFSM n) (hn : 0 < n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * n
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k
      ∧ m.run (k + P) = m.run k := by
  obtain ⟨i, hi, j, hj, hij, hsig, hrun⟩ := fsm_joint_collision m hn
  have hP : 0 < j 
... [trunc]
```

### Rank 111 (n=3): \`IFF, rfl\`
  *Specimen: \`survives_iff_odd\` from E213/Firmware/Atomicity/Alive.lean*
```lean
theorem survives_iff_odd (a : Nat) : Survives a ↔ a % 2 = 1 := by
  unfold Survives residue; rfl

/-- Both atom-types survive iff both multiplicities are odd. -/
```

### Rank 121 (n=3): \`decide, rfl, rw\`
  *Specimen: \`f9Lens_view_ab\` from E213/Hypervisor/Lens/Instances/F9.lean*
```lean
theorem f9Lens_view_ab :
    f9Lens.view (Raw.slash Raw.a Raw.b (by decide)) = F9.i := by
  show Raw.fold F9.one F9.i F9.mul (Raw.slash Raw.a Raw.b _) = F9.i
  rw [Raw.fold_slash F9.one F9.i F9.mul F9.mul_comm Raw.a Raw.b (by decide)]
  rfl
```

### Rank 131 (n=3): \`FORALL, IMPLIES, rfl\`
  *Specimen: \`add_sub_assoc\` from E213/Kernel/Tactic/Nat213.lean*
```lean
theorem add_sub_assoc :
    ∀ (a : Nat) {b c : Nat}, c ≤ b → a + b - c = a + (b - c)
  | _, _, 0, _ => rfl
  | a, b+1, c+1, h =>
    let h' : c ≤ b := Nat.le_of_succ_le_succ h
    let ih : a + b - c = a + (b - c) := add_sub_assoc a h'
    -- a + (b+1) - (c+1) = (a + b + 1) - (c+1) [Nat.add_succ]
   
... [trunc]
```

### Rank 141 (n=3): \`AND, FORALL, decide\`
  *Specimen: \`phase_CA_delta_sq_zero\` from E213/Math/Cohomology/Delta/SqZero.lean*
```lean
theorem phase_CA_delta_sq_zero :
    (∀ i : Fin (binom 5 3), delta (delta (Cochain.zero 5 1)) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (delta vertex0_n5) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (delta vertex2_n5) i = false)
    ∧ (∀ i : Fin (binom 5 4), delta (delta edge01_n5) i = false
... [trunc]
```

### Rank 151 (n=3): \`EXISTS, anon, cases, exact, rfl, rw\`
  *Specimen: \`nat_trichotomy\` from E213/Math/ModArith/PureNatMod3.lean*
```lean
theorem nat_trichotomy (n : Nat) :
    (∃ k, n = 3 * k) ∨ (∃ k, n = 3 * k + 1) ∨ (∃ k, n = 3 * k + 2) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m ih =>
      cases ih with
      | inl h =>
          obtain ⟨k, hk⟩ := h
          right; left
          exact ⟨k, by rw [hk]⟩
 
... [trunc]
```

### Rank 161 (n=2): \`FORALL, IMPLIES, anon, exact, intro, rw\`
  *Specimen: \`view_factors_through_morphism\` from E213/Hypervisor/Lens/Compose/Morphism.lean*
```lean
theorem view_factors_through_morphism {α β : Type}
    (L : Lens α) (M : Lens β) (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) :
    ∀ r : Raw, M.view r = h (L.view r) := by
  obtain ⟨hba, h
... [trunc]
```

### Rank 171 (n=2): \`exact, intro, rfl, rw\`
  *Specimen: \`tierLens_view_eq_tier\` from E213/Hypervisor/Lens/Leaves/DepthJoin.lean*
```lean
theorem tierLens_view_eq_tier (r : Raw) : tierLens.view r = tier r := by
  induction r using Raw.rec with
  | a => unfold tier tierLens; show 0 = (if Lens.leaves.view Raw.a = 1 then 0 else _); rfl
  | b => unfold tier tierLens; show 0 = (if Lens.leaves.view Raw.b = 1 then 0 else _); rfl
  | slash x 
... [trunc]
```

### Rank 181 (n=2): \`cases, exact, intro, rw\`
  *Specimen: \`e_partial_neq_third_a\` from E213/Math/Cauchy/EulerSharperPure.lean*
```lean
theorem e_partial_neq_third_a (a : Nat) (ha : a ≥ 1) (N : Nat) (hN : N ≥ 4) :
    3 * eulerNum N ≠ a * eulerDen N := by
  intro heq
  have h_lower : 3 * eulerNum N ≥ 8 * eulerDen N + 1 :=
    euler_sharper_8_3_pure N hN
  have h_upper : 3 * eulerDen N ≥ eulerNum N + 1 :=
    EulerCombinatorialPure.e
... [trunc]
```

### Rank 191 (n=2): \`AND, EXISTS, FORALL, IMPLIES, NEG, exact, intro, match, rw\`
  *Specimen: \`aperiodic_bits_imp_not_ArithFSM2\` from E213/Math/Cohomology/Dyadic/ArithFSM/Hardness.lean*
```lean
theorem aperiodic_bits_imp_not_ArithFSM2 (bs : Nat → Bool)
    (h_aperiodic : ∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) :
    ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n),
      ¬ (∀ k, m.bits k = bs k) := by
  intro n hn m h_match
  apply aperiodic_bits_imp_not_BitFSM bs h_aperiodic (n * n) (m.t
... [trunc]
```
