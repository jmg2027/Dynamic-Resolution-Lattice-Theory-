# Top 10 slot-combinations — 6 specimens each

## Combo: `decide`  (1375 theorems)

### \`add_two_ne_self\` (E213/Firmware/Atomicity/FiveHelpers.lean)
```lean
theorem add_two_ne_self (b : Nat) : b + 2 ≠ b := fun h =>
  let h_eq : b + 2 = b + 0 := h.trans (Nat.add_zero b).symm
  absurd (add_left_cancel h_eq) (by decide)

/-- `a + 3 ≠ a`. -/
```

### \`leaves_equates\` (E213/Hypervisor/Lens/Instances/AB.lean)
```lean
theorem leaves_equates : Lens.leaves.view rAAB = Lens.leaves.view rABB := by decide
```

### \`F3\` (E213/Hypervisor/Lens/Instances/F9.lean)
```lean
abbrev F3 := Fin 3
```

### \`parity_equates_ab\` (E213/Hypervisor/Lens/Instances/ParityXorIncomparable.lean)
```lean
theorem parity_equates_ab :
    parityLens.view Raw.a = parityLens.view Raw.b := by decide
```

### \`rawACharLens_distinguishes_a_b\` (E213/Hypervisor/Lens/Instances/RawAChar.lean)
```lean
theorem rawACharLens_distinguishes_a_b :
    rawACharLens.view Raw.a ≠ rawACharLens.view Raw.b := by decide
```

### \`leaves_equates\` (E213/Hypervisor/Lens/Leaves/DepthIncomparable.lean)
```lean
theorem leaves_equates :
    Lens.leaves.view rDeep = Lens.leaves.view rBalanced := by decide

/-- Lens.depth distinguishes them (4 vs 3). -/
```


## Combo: `AND, decide`  (349 theorems)

### \`reduced_betti_d4_contractible\` (E213/Math/Cohomology/BettiKernel.lean)
```lean
theorem reduced_betti_d4_contractible :
    kerSizeDelta 5 0 = 1 ∧ kerSizeDelta 5 1 = 2 := by decide

/-- Smoke: |Cᵏ| = 2^(binom n k) for n=5, k=0..2. -/
```

### \`edge0_endpoints\` (E213/Math/Cohomology/Bipartite/V32.lean)
```lean
theorem edge0_endpoints :
    srcFin ⟨0, by decide⟩ = ⟨0, by decide⟩
    ∧ tgtFin ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide

/-- Edge 11 (last) has S-vertex 2 and T-vertex 4. -/
```

### \`phase_CE_capstone\` (E213/Math/Cohomology/Bipartite/V32Betti.lean)
```lean
theorem phase_CE_capstone :
    kerSizeDelta0 = 2
    ∧ 2^5 = 32
    ∧ 2^12 = 4096
    ∧ 16 * 256 = 4096
    ∧ 256 = 2^8
    ∧ 8 = 3 * 3 - 1 := by decide
```

### \`chi_N_pattern\` (E213/Math/Cohomology/ClosureExtension.lean)
```lean
theorem chi_N_pattern :
    E213.Math.Cohomology.EulerClosed.chi_delta4 = 1
    ∧ E213.Math.Cohomology.EulerClosed.chi_two_glued = 2
    ∧ chi_3_glued = 3
    ∧ chi_4_glued = 4 := by decide

/-- ★ N from topology: each Δ⁴ glued (sharing full ∂Δ⁴) adds
    1 to χ.  Specific N value (= cosmos size) sets topology
    type but isn't atomic-derived. -/
```

### \`cup_v0_v0_concrete\` (E213/Math/Cohomology/Cup/Core.lean)
```lean
theorem cup_v0_v0_concrete :
    cup 5 1 1 v0_5 v0_5 ⟨0, by decide⟩ = false
    ∧ cup 5 1 1 v0_5 v0_5 ⟨1, by decide⟩ = false := by decide

/-- All-ones cochain at (5, 1). -/
```

### \`diamond_audit_falsifier_coupling\` (E213/Math/Cohomology/DiamondAudit.lean)
```lean
theorem diamond_audit_falsifier_coupling :
    NS = 3 ∧ NT = 2 ∧ d = 5 := by decide
```


## Combo: `rfl`  (331 theorems)

### \`pairSize_nondecomposable\` (E213/Firmware/Atomicity/PrimitiveSizes.lean)
```lean
theorem pairSize_nondecomposable : NonDecomposable pairSize :=
  (non_decomposable_iff 2).mpr (Or.inl rfl)

/-- The first closure size is non-decomposable. -/
```

### \`Raw\` (E213/Firmware/Raw/Swap.lean)
```lean
def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩
```

### \`Raw\` (E213/Firmware/RawLevels.lean)
```lean
def Raw.level1_set : List Raw :=
  [Raw.a, Raw.b, Raw.slash Raw.a Raw.b (by decide)]

/-- Level-2 additions: the Raw terms `a/(a/b)`, `b/(a/b)`. -/
```

### \`boolToConstLens_true\` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)
```lean
theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl
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
    ∀ r : Raw, f r = L.view r := by
  intro r
  induction r using R
... [truncated]
```

### \`f9Lens_view_a\` (E213/Hypervisor/Lens/Instances/F9.lean)
```lean
theorem f9Lens_view_a : f9Lens.view Raw.a = F9.one := rfl

/-- Concrete view check: view b = i. -/
```


## Combo: `(empty / pure term-mode)`  (229 theorems)

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
      | slash x₂ y₂ =>
          simp only [Tree.cmp]
          co
... [truncated]
```

### \`Tree_cmp_props\` (E213/Firmware/Raw/CmpIndependence.lean)
```lean
theorem Tree_cmp_props : CmpProps Tree.cmp where
  eq_iff := Tree.cmp_eq_iff
  swap := Tree.cmp_swap

/-- Reverse of cmp: cmpRev x y := (cmp x y).swap. -/
```

### \`Raw\` (E213/Firmware/Raw/Levels.lean)
```lean
theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property
```

### \`Raw\` (E213/Firmware/Raw/Signed.lean)
```lean
theorem Raw.fold_signed_swap (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r :=
  Tree.fold_signed_swap r.val r.property
```

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


## Combo: `AND, anon, decide, refine`  (214 theorems)

### \`mul_generators_ne_zero\` (E213/Math/CayleyDickson/CDDouble.lean)
```lean
theorem mul_generators_ne_zero :
    I' * J ≠ 0 ∧ J * I' ≠ 0 ∧ I' * I' ≠ 0 ∧ J * J ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
```

### \`mul_generators_ne_zero\` (E213/Math/CayleyDickson/Cayley.lean)
```lean
theorem mul_generators_ne_zero :
    I' * J' ≠ 0 ∧ J' * L ≠ 0 ∧ I' * L ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide
```

### \`alpha_3_two_derivations\` (E213/Math/Cohomology/Audit.lean)
```lean
theorem alpha_3_two_derivations :
    E213.Physics.Couplings.PhotonKernel.b_1 = 8
    ∧ E213.Math.Cohomology.Bipartite.V32Betti.kerSizeDelta0 = 2
    ∧ 16 * 256 = 4096 := by
  refine ⟨E213.Physics.Couplings.PhotonKernel.b_1_eq_8, ?_, ?_⟩ <;> decide
```

### \`fib_pisano_predict_correct\` (E213/Math/Cohomology/Dyadic/Fib/PisanoCapstone.lean)
```lean
theorem fib_pisano_predict_correct :
    fib_pisano_predict 3 (by decide) = 8
    ∧ fib_pisano_predict 5 (by decide) = 20
    ∧ fib_pisano_predict 7 (by decide) = 16
    ∧ fib_pisano_predict 11 (by decide) = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ The Legendre lens-driven Fibonacci predictor REALISES
    the actual Fibonacci bit 
... [truncated]
```

### \`pisano_predict_proper_correct\` (E213/Math/Cohomology/Dyadic/Pell/ProperBridge.lean)
```lean
theorem pisano_predict_proper_correct :
    pisano_predict_proper 3 (by decide) = 8
    ∧ pisano_predict_proper 5 (by decide) = 12
    ∧ pisano_predict_proper 7 (by decide) = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ Pell proper Legendre-Pisano bridge — both branch types. -/
```

### \`pisano_predict_correct\` (E213/Math/Cohomology/Dyadic/Pisano/Predictor.lean)
```lean
theorem pisano_predict_correct :
    pisano_predict 3 (by decide) = 4
    ∧ pisano_predict 5 (by decide) = 10
    ∧ pisano_predict 7 (by decide) = 8
    ∧ pisano_predict 11 (by decide) = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ The Legendre lens-driven predictor PREDICTS the
    actual Pell bit periods at all four primes — a single
... [truncated]
```


## Combo: `exact, rw`  (105 theorems)

### \`Raw\` (E213/Firmware/Raw/Swap.lean)
```lean
def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩
```

### \`composite_slash\` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)
```lean
theorem composite_slash (x y : Raw) (h : x ≠ y) :
    composite (Raw.slash x y h) = lensXor (composite x) (composite y) := by
  unfold composite
  rw [@universalMorphism_slash Bool boolXorHasDistinguishing x y h]
  exact boolToConstLens_xor _ _
```

### \`constComposite_slash\` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)
```lean
theorem constComposite_slash (α : Type) [d : HasDistinguishing α]
    (x y : Raw) (h : x ≠ y) :
    constComposite α (Raw.slash x y h) =
      lensCombineGeneric d.combine (constComposite α x) (constComposite α y) := by
  unfold constComposite
  rw [@universalMorphism_slash α d x y h]
  exact (lensCombineGeneric_const d.combine _ _).symm
```

### \`joinEquiv_subset_tierLens\` (E213/Hypervisor/Lens/Leaves/DepthJoin.lean)
```lean
theorem joinEquiv_subset_tierLens (r r' : Raw)
    (h : JoinEquiv Lens.leaves Lens.depth r r') :
    tierLens.equiv r r' := by
  show tierLens.view r = tierLens.view r'
  rw [tierLens_view_eq_tier, tierLens_view_eq_tier]
  exact tier_invariant r r' h
```

### \`euler_upper_step\` (E213/Math/Cauchy/EulerGenericPure.lean)
```lean
theorem euler_upper_step (j b k : Nat) (hk : k ≥ b)
    (h_inv : j * eulerDen k ≥ b * eulerNum k + 1) :
    j * eulerDen (k + 1) ≥ b * eulerNum (k + 1) + 1 := by
  show j * ((k + 1) * eulerDen k) ≥ b * ((k + 1) * eulerNum k + 1) + 1
  have h_lhs : j * ((k+1) * eulerDen k) = (k+1) * (j * eulerDen k) := by
    rw [← mul_assoc, Nat.mul_comm j (k+1), m
... [truncated]
```

### \`eulerDen_pos_pure\` (E213/Math/Cauchy/EulerSharperPure.lean)
```lean
theorem eulerDen_pos_pure (N : Nat) : eulerDen N ≥ 1 := by
  induction N with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
      show eulerDen (k + 1) ≥ 1
      show (k + 1) * eulerDen k ≥ 1
      have h_kp : k + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_mul : (k + 1) * eulerDen k ≥ (k + 1) * 1 :=
        Nat.mul_le_mul_left (k+1) 
... [truncated]
```


## Combo: `FORALL, decide`  (90 theorems)

### \`bool_not_involutive\` (E213/Hypervisor/Lens/Instances/Bool.lean)
```lean
theorem bool_not_involutive : ∀ u : Bool, !(!u) = u := by decide

/-- `not` on Bool is NOT the identity. -/
```

### \`delta0_zero\` (E213/Math/Cohomology/Bipartite/V32.lean)
```lean
theorem delta0_zero : ∀ e : Fin 12, delta0 zeroV e = false := by decide

/-- δ₀(allTrueV) = zero edge cochain (constant in ker). -/
```

### \`cup_zero_left_5_1_1\` (E213/Math/Cohomology/Cup/Core.lean)
```lean
theorem cup_zero_left_5_1_1 :
    ∀ i : Fin (binom 5 2),
      cup 5 1 1 (Cochain.zero 5 1) v0_5 i = false := by decide

/-- Smoke: cup with zero right = zero. -/
```

### \`leibniz_v0_v0_pointwise\` (E213/Math/Cohomology/Cup/Leibniz.lean)
```lean
theorem leibniz_v0_v0_pointwise :
    ∀ i : Fin (binom 5 3),
      delta (cup 5 1 1 v0_5 v0_5) i
        = xor (cup 5 2 1 (delta v0_5) v0_5 i)
              (cup 5 1 2 v0_5 (delta v0_5) i) := by decide

/-- Leibniz on (all_true_5_1 ⌣ v0_5). -/
```

### \`cup_unit_left_v0\` (E213/Math/Cohomology/Cup/Ring.lean)
```lean
theorem cup_unit_left_v0 :
    ∀ i : Fin (binom 5 1),
      cup 5 0 1 unit_5 v0_5 i = v0_5 i := by decide

/-- Right unit: v0_5 ⌣ ε = v0_5. -/
```

### \`basis_leibniz_5_1_2\` (E213/Math/Cohomology/CupAW/BasisLeibniz.lean)
```lean
theorem basis_leibniz_5_1_2 :
    ∀ i : Fin 5, ∀ k : Fin 10, ∀ j : Fin 10,
      delta (cupAW 5 1 2 (basis 5 1 i) (basis 5 2 k)) j
        = xor (cupAW 5 2 2 (delta (basis 5 1 i)) (basis 5 2 k) j)
              (cupAW 5 1 3 (basis 5 1 i) (delta (basis 5 2 k)) j) := by
  decide

/-- ★★★ Basis-pair Leibniz at (5, 2, 2) — 100 × 5 = 500-case decide.
  
... [truncated]
```


## Combo: `rw`  (80 theorems)

### \`depth_swap_invariant\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)
```lean
theorem depth_swap_invariant (r : Raw) :
    Lens.depth.view (Raw.swap r) = Lens.depth.view r := by
  show Raw.fold 0 0 (fun a b => 1 + max a b) (Raw.swap r)
     = Raw.fold 0 0 (fun a b => 1 + max a b) r
  rw [Raw.fold_eq_depth, Raw.fold_eq_depth, Raw.swap_depth]

/-- **Leaves lens is swap-blind.** Same base value for `a` and
    `b`. The Lens cou
... [truncated]
```

### \`constComposite_a\` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)
```lean
theorem constComposite_a (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.a = constLens d.a := by
  unfold constComposite
  rw [@universalMorphism_a α d]
```

### \`universalMorphism_first\` (E213/Hypervisor/Lens/Instances/Pair.lean)
```lean
theorem universalMorphism_first (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    Prod.fst (@universalMorphism (α × β) (pairHasDistinguishing α β) r)
      = universalMorphism α r := by
  rw [universalMorphism_pair_commute]
```

### \`universalMorphism_commute\` (E213/Hypervisor/Lens/Morphism/BoolProp.lean)
```lean
theorem universalMorphism_commute (r : Raw) :
    @universalMorphism Prop propAsDistinguishingAnd r
      = boolToProp (universalMorphism Bool r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingAnd Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishingAnd
      have h2 : un
... [truncated]
```

### \`constLens_equiv_total\` (E213/Hypervisor/Lens/Properties/ConstLensTotalKernel.lean)
```lean
theorem constLens_equiv_total {α : Type} (e : α) (x y : Raw) :
    (constLens e).equiv x y := by
  unfold Lens.equiv
  rw [constLens_view, constLens_view]
```

### \`prod_equates\` (E213/Hypervisor/Lens/Properties/ProdBelowId.lean)
```lean
theorem prod_equates :
    (prodLens Lens.leaves Lens.depth).view rA
      = (prodLens Lens.leaves Lens.depth).view rB := by
  rw [prodLens_view _ _ leaves_sym depth_sym,
      prodLens_view _ _ leaves_sym depth_sym,
      leaves_equal, depth_equal]

/-- **idLens distinguishes them** (they are unequal Raw). -/
```


## Combo: `IMPLIES`  (63 theorems)

### \`funextLens_inhabited\` (E213/Hypervisor/Lens/AxiomLenses/Bridges/Funext.lean)
```lean
theorem funextLens_inhabited {α β : Type} (f g : α → β) :
    funextLens f g := funext
```

### \`pointwiseEq_symm\` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)
```lean
theorem pointwiseEq_symm {α β : Type} {f g : α → β}
    (h : pointwiseEq f g) : pointwiseEq g f :=
  fun x => (h x).symm
```

### \`boundedEq_symm\` (E213/Hypervisor/Lens/Instances/BoundedContext.lean)
```lean
theorem boundedEq_symm {N : Nat} {α : Type} {f g : Nat → α}
    (h : boundedEq N f g) : boundedEq N g f := fun i => (h i).symm
```

### \`tailCong_slash_cong\` (E213/Hypervisor/Lens/Instances/Cauchy.lean)
```lean
theorem tailCong_slash_cong (xs : Nat → Raw) (N : Nat)
    (x x' y y' : Raw) (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hxx' : TailCong xs N x x') (hyy' : TailCong xs N y y') :
    TailCong xs N (Raw.slash x y hxy) (Raw.slash x' y' hx'y') :=
  TailCong.slash_cong hxy hx'y' hxx' hyy'

/-- **Limit Lens**: the universalLens of TailCong is the limit Lens of

... [truncated]
```

### \`entryEq_symm\` (E213/Hypervisor/Lens/Instances/CochainEntry.lean)
```lean
theorem entryEq_symm {N : Nat} {σ τ : Fin N → Bool}
    (h : entryEq σ τ) : entryEq τ σ := fun i => (h i).symm
```

### \`pointwiseEq_symm\` (E213/Hypervisor/Lens/Instances/PointwiseProjection.lean)
```lean
theorem pointwiseEq_symm {f g : Nat → Nat → Bool}
    (h : pointwiseEq f g) : pointwiseEq g f :=
  fun m k => (h m k).symm
```


## Combo: `IMPLIES, rfl`  (60 theorems)

### \`transport_a\` (E213/Firmware/Raw/CmpIndependence.lean)
```lean
theorem transport_a (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    transport cmp1 cmp2 h1 h2 (RawBy.a cmp1) = RawBy.a cmp2 := rfl

/-- transport of RawBy.b. -/
```

### \`Raw\` (E213/Firmware/Raw/Fold.lean)
```lean
def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl
```

### \`pointwiseEq_refl\` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)
```lean
theorem pointwiseEq_refl {α β : Type} (f : α → β) : pointwiseEq f f :=
  fun _ => rfl
```

### \`lensCombineGeneric_const\` (E213/Hypervisor/Lens/Compose/OnLensImageGeneric.lean)
```lean
theorem lensCombineGeneric_const {α : Type} (c : α → α → α) (a b : α) :
    lensCombineGeneric c (constLens a) (constLens b) = constLens (c a b) := by
  unfold lensCombineGeneric constLens; rfl
```

### \`boundedEq_refl\` (E213/Hypervisor/Lens/Instances/BoundedContext.lean)
```lean
theorem boundedEq_refl (N : Nat) {α : Type} (f : Nat → α) :
    boundedEq N f f := fun _ => rfl
```

### \`entryEq_refl\` (E213/Hypervisor/Lens/Instances/CochainEntry.lean)
```lean
theorem entryEq_refl {N : Nat} (σ : Fin N → Bool) : entryEq σ σ :=
  fun _ => rfl
```

