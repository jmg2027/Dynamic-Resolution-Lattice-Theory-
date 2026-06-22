# Existential theorems (∃) — 170 decls

(Auto-extracted by `tools/theorem_inspect.py`.)

> **STALE 2026-05-13**: paths like `Firmware/`, `Hypervisor/`,
> `Lib/Math/Infinity/`, `Lens/Diagonal`, `Lens/Refines`,
> `Meta/UniversalLens` reflect the pre-rename state.  Re-run
> `tools/theorem_inspect.py` to refresh against the current 4-ring +
> Meta layout (Term/Theory/Lens/Lib + Meta).

## `reachable3_only_object` (E213/Firmware/Atomicity/ArityForcing.lean)

```lean
theorem reachable3_only_object {x : Raw3} (h : Reachable3 x) :
    ∃ i : Fin 2, x = .object i := by
  induction h with
  | base i => exact ⟨i, rfl⟩
  | @step x y z _ _ _ hxy hyz hxz ihx ihy ihz =>
      obtain ⟨ix, rfl⟩ := ihx
      obtain ⟨iy, rfl⟩ := ihy
      obtain ⟨iz, rfl⟩ := ihz
      exfalso
      have hxy' : ix.val ≠ iy.val :=
        fun h => hxy (congrArg Raw3.object (Fin.ext h))
      have hyz' : iy.val ≠ iz.val :=
        fun h => hyz (congrArg Raw3.object (Fin.ext h))
      have hxz' : ix.val ≠ iz.val :=
        fun h => hxz (congrArg Raw3.object (Fin.ext h))
      -- Pigeonhole:
... [truncated]
```

## `reachable_base_only` (E213/Firmware/Atomicity/ArityForcingGeneral.lean)

```lean
theorem reachable_base_only {N k : Nat} (h : N < k) :
    ∀ {x : RawNk N k}, ReachableNk x → ∃ i : Fin N, x = .object i := by
  intro x hr
  exact ⟨getBase x (reachable_isBase h hr), getBase_eq x _⟩

/-- Corollary: no rel-term is ever Reachable when `N < k`. -/
```

## `Lens` (E213/Hypervisor/Lens/Foundations/Initiality.lean)

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

## `cauchy_iff_eventually_class` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem cauchy_iff_eventually_class {α : Type} (L : Lens α)
    (xs : Nat → Raw) :
    LensCauchy L xs ↔ ∃ c, EventuallyClass L xs c := by
  constructor
  · intro ⟨N, h⟩
    refine ⟨L.view (xs N), N, ?_⟩
    intro n hn
    exact h n N hn (Nat.le_refl N)
  · intro ⟨c, N, h⟩
    refine ⟨N, ?_⟩
    intro m n hm hn
    show L.view (xs m) = L.view (xs n)
    rw [h m hm, h n hn]

/-- Uniqueness of the limit class: two EventuallyClasses are equal. -/
```

## `cauchy_data_of` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem cauchy_data_of {α : Type} (L : Lens α) (xs : Nat → Raw)
    (h : LensCauchy L xs) :
    ∃ cd : CauchyData L xs, True := by
  obtain ⟨N, hN⟩ := h
  exact ⟨⟨N, hN⟩, trivial⟩
```

## `pointwise_limit_match` (E213/Hypervisor/Lens/Instances/Cauchy.lean)

```lean
theorem pointwise_limit_match {ι : Type} (F : ι → (α : Type) × Lens α)
    (xs : Nat → Raw)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (la : LimitAssignment F xs) (i : ι) :
    ∃ N, ∀ n, n ≥ N → (iProdLens F).view (xs n) i = la.limit i := by
  refine ⟨(la.data i).N, ?_⟩
  intro n hn
  rw [iProdLens_view F hAllSym (xs n)]
  exact limitClass_eq_tail (F i).2 xs (la.data i) n hn
```

## `parityXor_image_ge_three` (E213/Hypervisor/Lens/Instances/CompoundBool.lean)

```lean
theorem parityXor_image_ge_three :
    ∃ r₁ r₂ r₃ : Raw,
      parityXorLens.view r₁ ≠ parityXorLens.view r₂ ∧
      parityXorLens.view r₁ ≠ parityXorLens.view r₃ ∧
      parityXorLens.view r₂ ≠ parityXorLens.view r₃ := by
  refine ⟨Raw.a, Raw.b, ab, ?_, ?_, ?_⟩
  all_goals decide
```

## `maxLens_R4_fails` (E213/Hypervisor/Lens/Instances/Max.lean)

```lean
theorem maxLens_R4_fails :
    ¬ ∃ conj : Nat → Nat, SwapMatching maxLens conj := by
  rintro ⟨conj, hmatch⟩
  have hswap := hmatch.2.2
  have h1_from_b : conj 1 = 0 := by
    have h := hswap Raw.b
    show conj 1 = 0
    rw [show maxLens.view Raw.b = 1 from rfl,
        show Raw.swap Raw.b = Raw.a from Raw.swap_b,
        show maxLens.view Raw.a = 0 from rfl] at h
    exact h.symm
  have h1_from_ab : conj 1 = 1 := by
    let r : Raw := Raw.slash Raw.a Raw.b (by decide)
    have h := hswap r
    rw [show maxLens.view r = 1 from rfl,
        slash_ab_swap_fixed] at h
    exact h.symm
  rw [h1_f
... [truncated]
```

## `negSqLens_not_collapse` (E213/Hypervisor/Lens/Instances/NegSq.lean)

```lean
theorem negSqLens_not_collapse : ¬ ∃ e : Bool, Collapse negSqLens e := by
  intro ⟨e, hC⟩
  have h1 : (!true : Bool) = e := hC true
  have h2 : (!false : Bool) = e := hC false
  have hfalse : (!true : Bool) = false := rfl
  have htrue : (!false : Bool) = true := rfl
  rw [hfalse] at h1
  rw [htrue] at h2
  rw [← h1] at h2
  cases h2

/-- combine is symmetric (satisfies the Lens AXIOM requirement). -/
```

## `parityLens_R4_fails` (E213/Hypervisor/Lens/Instances/Parity.lean)

```lean
theorem parityLens_R4_fails :
    ¬ ∃ conj : Bool → Bool, SwapMatching parityLens conj := by
  rintro ⟨conj, hmatch⟩
  have hsw : ∀ r : Raw, parityLens.view (Raw.swap r) = parityLens.view r :=
    parityLens_swap_invariant
  have hfix : ∀ r : Raw, conj (parityLens.view r) = parityLens.view r :=
    fun r => swap_invariant_R4_fixes_image hsw hmatch r
  have htrue : conj true = true := hfix Raw.a
  have hfalse : conj false = false := by
    have h := hfix parityLens_sample_even
    rw [parityLens_sample_even_view] at h
    exact h
  have hid : conj = id := by
    funext u; cases u
    · exact hf
... [truncated]
```

## `fin3_image_strict` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem fin3_image_strict :
    ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x := by
  refine ⟨2, ?_⟩
  intro ⟨r, hr⟩
  rcases fin3_image_in_01 r with h | h
  · rw [h] at hr; exact absurd hr (by decide)
  · rw [h] at hr; exact absurd hr (by decide)
```

## `bool_image_surjective` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem bool_image_surjective :
    ∀ b : Bool, ∃ r : Raw, universalMorphism Bool r = b := by
  intro b
  cases b with
  | true => exact ⟨Raw.a, universalMorphism_a Bool⟩
  | false => exact ⟨Raw.b, universalMorphism_b Bool⟩
```

## `image_contains_a` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem image_contains_a (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.a :=
  ⟨Raw.a, universalMorphism_a α⟩

/-- The image always contains d.b. -/
```

## `image_contains_b` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem image_contains_b (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.b :=
  ⟨Raw.b, universalMorphism_b α⟩

/-- The combine of distinct image elements is also in the image —
    direct application of Raw.slash. -/
```

## `image_closed_under_distinct_combine` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem image_closed_under_distinct_combine (α : Type) [d : HasDistinguishing α]
    (rx ry : Raw) (h : rx ≠ ry) :
    ∃ r : Raw,
      universalMorphism α r
        = d.combine (universalMorphism α rx) (universalMorphism α ry) :=
  ⟨Raw.slash rx ry h, universalMorphism_slash α rx ry h⟩
```

## `nat_image_zero` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem nat_image_zero : ∃ r : Raw, universalMorphism Nat r = 0 :=
  ⟨Raw.a, universalMorphism_a Nat⟩
```

## `nat_image_one` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem nat_image_one : ∃ r : Raw, universalMorphism Nat r = 1 :=
  ⟨Raw.b, universalMorphism_b Nat⟩

/-- 0 + 1 = 1 via slash a b. -/
```

## `nat_surjective_with_form` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem nat_surjective_with_form : ∀ n : Nat, ∃ r : Raw,
    universalMorphism Nat r = n ∧
    (r = Raw.a ∨ ∃ x y h, r = Raw.slash x y h) := by
  intro n
  induction n with
  | zero => exact ⟨Raw.a, universalMorphism_a Nat, Or.inl rfl⟩
  | succ n ih =>
      obtain ⟨r, hr_view, hr_form⟩ := ih
      have h_ne : r ≠ Raw.b := natWitness_ne_b_helper r hr_form
      have h_b_ne_r : Raw.b ≠ r := Ne.symm h_ne
      refine ⟨Raw.slash Raw.b r h_b_ne_r, ?_, Or.inr ⟨Raw.b, r, h_b_ne_r, rfl⟩⟩
      rw [universalMorphism_slash Nat Raw.b r h_b_ne_r,
          universalMorphism_b Nat, hr_view]
      show 1 +
... [truncated]
```

## `nat_image_surjective` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem nat_image_surjective :
    ∀ n : Nat, ∃ r : Raw, universalMorphism Nat r = n := by
  intro n
  obtain ⟨r, hview, _⟩ := nat_surjective_with_form n
  exact ⟨r, hview⟩
```

## `int_image_strict` (E213/Hypervisor/Lens/Instances/Reach.lean)

```lean
theorem int_image_strict :
    ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x := by
  refine ⟨-1, ?_⟩
  intro ⟨r, hr⟩
  have h_nonneg : 0 ≤ universalMorphism Int r := int_image_nonneg r
  rw [hr] at h_nonneg
  exact absurd h_nonneg (by decide)
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

## `leavesModNat_kernel_neq` (E213/Hypervisor/Lens/Kernel/CardinalityLB.lean)

```lean
theorem leavesModNat_kernel_neq (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hne : m ≠ k) :
    ∃ r r' : Raw,
      ¬ ((leavesModNat m).view r = (leavesModNat m).view r' ↔
          (leavesModNat k).view r = (leavesModNat k).view r') := by
  -- WLOG m > k OR k > m.  In each case, the larger one is not divided by the smaller.
  -- m > k: m % k ≠ 0 (since k < m and m ≠ multiple of k).  Hmm, m might be a multiple.
  -- Actually we need: ¬ k ∣ m OR ¬ m ∣ k.
  rcases Nat.lt_or_ge m k with hlt | hge
  · -- m < k: m ∤ k? not always true.  Try the other side: ¬ k ∣ m.  k > m → k ∤ m
    -- (since k ∤ m 
... [truncated]
```

## `fold_structured_lens_expressible` (E213/Hypervisor/Lens/Morphism/FoldStructured.lean)

```lean
theorem fold_structured_lens_expressible {α : Type} (f : Raw → α)
    (hfold : FoldStructured f) :
    ∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧ L.view = f := by
  obtain ⟨ba, bb, c, hba, hbb, hsym, hslash⟩ := hfold
  refine ⟨⟨ba, bb, c⟩, hsym, ?_⟩
  funext r
  have := Lens.view_unique (α := α) ⟨ba, bb, c⟩ hsym f hba hbb hslash r
  exact this.symm
```

## `lens_expressible_iff_fold_structured` (E213/Hypervisor/Lens/Morphism/FoldStructured.lean)

```lean
theorem lens_expressible_iff_fold_structured {α : Type} (f : Raw → α) :
    (∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧ L.view = f)
      ↔ FoldStructured f := by
  constructor
  · intro ⟨L, hsym, hview⟩
    rw [← hview]
    exact lens_view_fold_structured L hsym
  · exact fold_structured_lens_expressible f
```

## `exists_non_lens_expressible` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)

```lean
theorem exists_non_lens_expressible :
    ∃ f : Raw → Bool, ¬ IsLensExpressible f := by
  refine ⟨E213.Hypervisor.Lens.Morphism.DepthParityNotFold.depthParityFn, ?_⟩
  rw [isLensExpressible_iff_foldStructured]
  exact E213.Hypervisor.Lens.Morphism.DepthParityNotFold.depthParityFn_not_fold_structured
```

## `raw_initial` (E213/Hypervisor/Lens/Foundations/SemanticAtom.lean)

```lean
theorem raw_initial (α : Type) [d : HasDistinguishing α] :
    ∃ f : Raw → α,
      (f Raw.a = d.a) ∧
      (f Raw.b = d.b) ∧
      (∀ (x y : Raw) (h : x ≠ y),
        f (Raw.slash x y h) = d.combine (f x) (f y)) ∧
      (∀ g : Raw → α,
        g Raw.a = d.a →
        g Raw.b = d.b →
        (∀ (x y : Raw) (h : x ≠ y),
          g (Raw.slash x y h) = d.combine (g x) (g y)) →
        g = f) := by
  refine ⟨universalMorphism α, ?_, ?_, ?_, ?_⟩
  · exact universalMorphism_a α
  · exact universalMorphism_b α
  · intro x y h; exact universalMorphism_slash α x y h
  · intro g hga hgb hgslash
    fun
... [truncated]
```

## `allBelow` (E213/Kernel/Decide.lean)

```lean
def allBelow : Nat → (Nat → Bool) → Bool
  | 0,     _ => true
  | n+1,   p => (allBelow n p) && p n

/-- Bool version of ∃ x < n, p x. -/
```

## `ratio_one_below_orderProj_eventually` (E213/Math/Cauchy/Archimedean.lean)

```lean
theorem ratio_one_below_orderProj_eventually
    (m k : Nat) (hk : k ≥ 1) :
    ∃ N, ∀ n, n ≥ N →
      orderProj m k (n+1, n+2) = decide (k ≤ m) := by
  by_cases hkm : k ≤ m
  · -- k ≤ m case: always true
    refine ⟨0, ?_⟩
    intro n _
    unfold orderProj
    show decide ((n+1) * k ≤ (n+2) * m) = decide (k ≤ m)
    have h1 : (n+1) * k ≤ (n+1) * m := Nat.mul_le_mul_left (n+1) hkm
    have h2 : (n+1) * m ≤ (n+2) * m := Nat.mul_le_mul_right m (Nat.le_succ _)
    have h3 : (n+1) * k ≤ (n+2) * m := Nat.le_trans h1 h2
    exact (decide_eq_true h3).trans (decide_eq_true hkm).symm
  · -- k > m cas
... [truncated]
```

## `euler_orderCauchy_at_concrete` (E213/Math/Cauchy/EulerSeq.lean)

```lean
theorem euler_orderCauchy_at_concrete (m k : Nat) (hk : k ≥ 1)
    (hcase : 3 * k ≤ m ∨ m ≤ 2 * k) :
    ∃ N, ∀ p q, p ≥ N → q ≥ N →
      orderProj m k (abLens.view (eulerRaw p).val)
        = orderProj m k (abLens.view (eulerRaw q).val) := by
  refine ⟨2, ?_⟩
  intro p q hp hq
  rcases hcase with h3km | hm2k
  · rw [euler_orderProj_above_3 m k h3km p,
        euler_orderProj_above_3 m k h3km q]
  · rw [euler_orderProj_below_2 m k hk hm2k p hp,
        euler_orderProj_below_2 m k hk hm2k q hq]
```

## `orderCauchy_from_false_witness` (E213/Math/Cauchy/MonotonicBounded.lean)

```lean
theorem orderCauchy_from_false_witness (xs : Nat → Raw)
    (hmono : IsAbMonotonic xs) (hpos : IsAbPositiveB xs)
    (m k N₀ : Nat)
    (hN₀ : orderProj m k (abLens.view (xs N₀)) = false) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      orderProj m k (abLens.view (xs i))
        = orderProj m k (abLens.view (xs j)) := by
  refine ⟨N₀, ?_⟩
  intro i j hi hj
  rw [orderProj_false_propagates xs hmono hpos m k N₀ hN₀ i hi,
      orderProj_false_propagates xs hmono hpos m k N₀ hN₀ j hj]

/-- Constructive Cauchy at `(m, k)` given a "true forever" witness. -/
```

## `orderCauchy_from_true_forever` (E213/Math/Cauchy/MonotonicBounded.lean)

```lean
theorem orderCauchy_from_true_forever (xs : Nat → Raw)
    (m k : Nat)
    (h : ∀ n, orderProj m k (abLens.view (xs n)) = true) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      orderProj m k (abLens.view (xs i))
        = orderProj m k (abLens.view (xs j)) := by
  refine ⟨0, ?_⟩
  intro i j _ _; rw [h i, h j]
```

## `abLens_surjective` (E213/Math/Cauchy/PellSeq.lean)

```lean
theorem abLens_surjective (s a b : Nat) (hsum : a + b = s) (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ∃ r : Raw, abLens.view r = (a, b) :=
  let ⟨r, hr⟩ := abLens_witness s a b hsum ha hb
  ⟨r, hr⟩
```

## `pellRaw_cut_above` (E213/Math/Cauchy/PellSeq.lean)

```lean
theorem pellRaw_cut_above (m k : Nat) (hk : k ≥ 1) (hmsq : 2 * k * k < m * m) :
    ∃ N, ∀ n, n ≥ N →
      orderProj m k (abLens.view (pellRaw n).val) = true := by
  refine ⟨k, ?_⟩
  intro n hn
  rw [pellRaw_view]
  -- pellY n ≥ n + 2 ≥ n ≥ k
  have hyn : pellY n ≥ k :=
    Nat.le_trans hn (Nat.le_trans (Nat.le_add_right n 2) (pellY_lb n))
  have hyn_sq : k * k ≤ pellY n * pellY n := Nat.mul_le_mul hyn hyn
  exact pell_orderProj_above (pellX n) (pellY n) m k
    (pell_invariant n) hmsq hyn_sq

/-- **√2 cut from Pell Raw seq (below)**: when m² < 2k², orderProj is
    false for all n. -/
```

## `wallis_orderCauchy_at_concrete` (E213/Math/Cauchy/WallisSeq.lean)

```lean
theorem wallis_orderCauchy_at_concrete (m k : Nat) (hk : k ≥ 1)
    (hcase : 2 * k ≤ m ∨ m ≤ k) :
    ∃ N, ∀ p q, p ≥ N → q ≥ N →
      orderProj m k (abLens.view (wallisRaw p).val)
        = orderProj m k (abLens.view (wallisRaw q).val) := by
  refine ⟨1, ?_⟩
  intro p q hp hq
  rcases hcase with h2km | hmk
  · rw [wallis_orderProj_above_2 m k h2km p,
        wallis_orderProj_above_2 m k h2km q]
  · rw [wallis_orderProj_below_1 m k hk hmk p hp,
        wallis_orderProj_below_1 m k hk hmk q hq]
```

## `mul_not_commutative` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem mul_not_commutative : ∃ u v : Lipschitz, u * v ≠ v * u := by
  refine ⟨I', J, ?_⟩
  intro h
  rw [I_mul_J, J_mul_I] at h
  have hr : (⟨0, ZI.I⟩ : Lipschitz).im = (⟨0, ZI.negI⟩ : Lipschitz).im := by
    rw [h]
  have : ZI.I = ZI.negI := hr
  have : (1 : Int) = -1 := (ZI.mk.injEq ..).mp this |>.2
  exact absurd this (by decide)
```

## `CD_tower_drops` (E213/Math/CayleyDickson/CDTower.lean)

```lean
theorem CD_tower_drops :
    -- Layer 0 (ZI): R2 holds universally.
    (∀ u v : ZI, u * v = v * u)
    -- Layer 1 (Lipschitz): R2 FAILS.
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)
    -- Layer 2 (Cayley): associativity FAILS.
    ∧ (∃ u v w : Cayley, (u * v) * w ≠ u * (v * w))
    -- Layer 3 (Sedenion): R3 FAILS.
    ∧ (∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0) :=
  ⟨ZI.mul_comm,
   Lipschitz.mul_not_commutative,
   Cayley.mul_not_associative,
   Sedenion.R3_fails_on_sedenion⟩
```

## `CD_tower_extended` (E213/Math/CayleyDickson/CDTower.lean)

```lean
theorem CD_tower_extended :
    -- L0 is commutative
    (∀ u v : ZI, u * v = v * u)
    -- L1 is non-commutative
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)
    -- L2 is non-associative
    ∧ (∃ u v w : Cayley, (u * v) * w ≠ u * (v * w))
    -- L3 has zero divisors
    ∧ (∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0)
    -- L3 is non-alternative
    ∧ (∃ a b : Sedenion, (a * a) * b ≠ a * (a * b)) :=
  ⟨ZI.mul_comm,
   Lipschitz.mul_not_commutative,
   Cayley.mul_not_associative,
   Sedenion.R3_fails_on_sedenion,
   Sedenion.not_alternative⟩
```

## `CD_tower_full` (E213/Math/CayleyDickson/CDTower.lean)

```lean
theorem CD_tower_full :
    (∀ u v : ZI, u * v = v * u)                                -- L0 comm
    ∧ (∀ u v w : ZI, (u * v) * w = u * (v * w))                -- L0 assoc
    ∧ (∀ u v : ZI, ZI.normSq (u * v) = ZI.normSq u * ZI.normSq v) -- L0 comp
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)                       -- L1 NOT comm
    ∧ (∀ u v w : Lipschitz, (u * v) * w = u * (v * w))         -- L1 assoc
    ∧ (∀ u v : Lipschitz, Lipschitz.normSq (u * v)
                           = Lipschitz.normSq u * Lipschitz.normSq v) -- L1 comp
    ∧ (∀ u v : Lipschitz, u * v = 0 → u = 0 ∨ v = 0)           --
... [truncated]
```

## `mul_not_associative` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem mul_not_associative :
    ∃ u v w : Cayley, (u * v) * w ≠ u * (v * w) := by
  refine ⟨I', J', L, ?_⟩
  decide
```

## `mul_not_commutative` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem mul_not_commutative :
    ∃ u v : Cayley, u * v ≠ v * u := by
  refine ⟨I', J', ?_⟩
  decide
```

## `F2D` (E213/Math/CayleyDickson/F2CDTower.lean)

```lean
abbrev F2D := F2 × F2

/-- CD multiplication, char-2 version. -/
```

## `foldTotality` (E213/Math/CayleyDickson/R5Vacuity.lean)

```lean
theorem foldTotality {α : Type} (L : Lens α) (r : Raw) :
    ∃ a : α, L.view r = a :=
  ⟨L.view r, rfl⟩

/-- Corollary: R5' places **no** constraint on the Lens. Any
    `Lens α` satisfies it. -/
```

## `foldTotality_vacuous` (E213/Math/CayleyDickson/R5Vacuity.lean)

```lean
theorem foldTotality_vacuous {α : Type} :
    ∀ L : Lens α, ∀ r : Raw, ∃ a : α, L.view r = a :=
  fun L r => foldTotality L r
```

## `R3_fails_on_sedenion` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
theorem R3_fails_on_sedenion :
    ∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0 :=
  ⟨zd_left, zd_right, zd_left_ne_zero, zd_right_ne_zero,
   zd_product_zero⟩
```

## `mul_not_commutative` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
theorem mul_not_commutative :
    ∃ u v : Sedenion, u * v ≠ v * u := by
  refine ⟨I', J', ?_⟩; decide

/-- **Sedenion multiplication is not associative**
    (inherited via Cayley I', J', L). -/
```

## `mul_not_associative` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
theorem mul_not_associative :
    ∃ u v w : Sedenion, (u * v) * w ≠ u * (v * w) := by
  refine ⟨I', J', L', ?_⟩; decide
```

## `not_alternative` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
theorem not_alternative :
    ∃ a b : Sedenion, (a * a) * b ≠ a * (a * b) :=
  ⟨zd_left, zd_right, alt_fails_at_zd⟩
```

## `normSq_mul_fails` (E213/Math/CayleyDickson/SedenionHeavy.lean)

```lean
theorem normSq_mul_fails :
    ∃ u v : Sedenion, normSq (u * v) ≠ normSq u * normSq v := by
  refine ⟨zd_left, zd_right, ?_⟩
  rw [zd_product_zero, normSq_zero]
  decide
```

## `choice_as_lens_spec` (E213/Math/Choice/Resolved.lean)

```lean
theorem choice_as_lens_spec (E : Raw → Raw → Prop)
    (hrefl : ∀ r, E r r)
    (hsymm : ∀ r r', E r r' → E r' r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h')) :
    ∃ L : Lens (Raw → Prop),
      ∀ r r' : Raw, L.view r = L.view r' ↔ E r r' :=
  ⟨universalLens E,
   fun r r' => universalLens_kernel_eq_E E hrefl hsymm htrans hslash r r'⟩

/-- **Choice as a direct consequence of Lens instances**: for each
    slash-cong E, universalLens E is the explicit witnes
... [truncated]
```

## `algebraic_tier1_capstone` (E213/Math/Cohomology/Dyadic/AlgebraicCapstone.lean)

```lean
theorem algebraic_tier1_capstone :
    -- quadratic (Pell ArithFSM2) closure
    ((∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
      ∧ (∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k)
      ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM2 n),
          ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n)
            ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k)
      ∧ (∀ (bs : Nat → Bool),
          (∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) →
          ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n),
            ¬ (∀ k, m.bits k = bs k)))
    -- cubic (Tribonacci Arit
... [truncated]
```

## `dyadic_signature_capstone` (E213/Math/Cohomology/Dyadic/Archive/Capstone.lean)

```lean
theorem dyadic_signature_capstone :
    -- (1) Lossless: signatures match ⇔ bit streams match
    (∀ bs₁ bs₂ : Nat → Bool,
      (∀ k, signature bs₁ k = signature bs₂ k) ↔ (∀ k, bs₁ k = bs₂ k))
    -- (2) Backward: signature ev-periodic ⇒ bit stream ev-periodic
    ∧ (∀ (bs : Nat → Bool) (p N : Nat) (hp : 0 < p),
        (∀ n, n ≥ N → signature bs (n + p) = signature bs n)
          → ∀ n, n ≥ N → bs (n + p) = bs n)
    -- (3) Forward: bs ev-periodic ⇒ signature ev-periodic
    ∧ (∀ (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p),
        (∀ n, n ≥ N₀ → bs (n + p) = bs n)
          → ∃ N P, 0 < P

... [truncated]
```

## `aperiodic_bits_imp_not_ArithFSM2` (E213/Math/Cohomology/Dyadic/ArithFSM/Hardness.lean)

```lean
theorem aperiodic_bits_imp_not_ArithFSM2 (bs : Nat → Bool)
    (h_aperiodic : ∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) :
    ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n),
      ¬ (∀ k, m.bits k = bs k) := by
  intro n hn m h_match
  apply aperiodic_bits_imp_not_BitFSM bs h_aperiodic (n * n) (m.toBitFSM hn)
  intro k
  rw [toBitFSM_bits_eq hn m k]
  exact h_match k

/-- ★★★★★★ ArithFSM2-generable ⇒ eventually periodic. -/
```

## `ArithFSM2_generable_imp_eventually_periodic` (E213/Math/Cohomology/Dyadic/ArithFSM/Hardness.lean)

```lean
theorem ArithFSM2_generable_imp_eventually_periodic (bs : Nat → Bool) :
    (∃ (n : Nat) (hn : 0 < n) (m : ArithFSM2 n), ∀ k, m.bits k = bs k)
    → ∃ N P, 0 < P ∧ ∀ k, k ≥ N → bs (k + P) = bs k := by
  rintro ⟨n, hn, m, hmatch⟩
  apply BitFSM_generable_imp_eventually_periodic bs
  refine ⟨n * n, m.toBitFSM hn, ?_⟩
  intro k
  rw [toBitFSM_bits_eq hn m k]
  exact hmatch k
```

## `pellFSMmod11_signature_period_bound` (E213/Math/Cohomology/Dyadic/ArithFSM/Mod11.lean)

```lean
theorem pellFSMmod11_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 605
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod11.bits (k + P) = signature pellFSMmod11.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 11) (by decide) pellFSMmod11
  exact ⟨N, P, hP, hbound, hk⟩
```

## `pellFSMmod7_signature_period_bound` (E213/Math/Cohomology/Dyadic/ArithFSM/Mod7.lean)

```lean
theorem pellFSMmod7_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 245
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod7.bits (k + P) = signature pellFSMmod7.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 7) (by decide) pellFSMmod7
  exact ⟨N, P, hP, hbound, hk⟩
```

## `pellFSMmod2_signature_eventually_periodic` (E213/Math/Cohomology/Dyadic/ArithFSM/Signature.lean)

```lean
theorem pellFSMmod2_signature_eventually_periodic :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod2.bits (n + P) = signature pellFSMmod2.bits n :=
  signature_eventually_periodic_of_eventually_periodic_bits
    pellFSMmod2.bits 3 0 (by decide)
    (fun n _ => pellFSMmod2_bits_period_3 n)

/-- ★★★ Pell mod-3 signature is eventually periodic. -/
```

## `pellFSMmod3_signature_eventually_periodic` (E213/Math/Cohomology/Dyadic/ArithFSM/Signature.lean)

```lean
theorem pellFSMmod3_signature_eventually_periodic :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod3.bits (n + P) = signature pellFSMmod3.bits n :=
  signature_eventually_periodic_of_eventually_periodic_bits
    pellFSMmod3.bits 4 0 (by decide)
    (fun n _ => pellFSMmod3_bits_period_4 n)

/-- ★★★ Pell mod-5 signature is eventually periodic. -/
```

## `pellFSMmod5_signature_eventually_periodic` (E213/Math/Cohomology/Dyadic/ArithFSM/Signature.lean)

```lean
theorem pellFSMmod5_signature_eventually_periodic :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod5.bits (n + P) = signature pellFSMmod5.bits n :=
  signature_eventually_periodic_of_eventually_periodic_bits
    pellFSMmod5.bits 10 0 (by decide)
    (fun n _ => pellFSMmod5_bits_period_10 n)

/-- ★★★★★ All three Pell ArithFSM streams (mod 2, 3, 5) yield
    eventually periodic K_{3,2}^{(2)} signatures.  Tier 1 is captured
    inside the eventually-periodic class — no transcendental escape. -/
```

## `pell_family_signatures_eventually_periodic` (E213/Math/Cohomology/Dyadic/ArithFSM/Signature.lean)

```lean
theorem pell_family_signatures_eventually_periodic :
    (∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod2.bits (n + P) = signature pellFSMmod2.bits n)
    ∧ (∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod3.bits (n + P) = signature pellFSMmod3.bits n)
    ∧ (∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod5.bits (n + P) = signature pellFSMmod5.bits n) :=
  ⟨pellFSMmod2_signature_eventually_periodic,
   pellFSMmod3_signature_eventually_periodic,
   pellFSMmod5_signature_eventually_periodic⟩
```

## `arithFSM2_signature_period_bound` (E213/Math/Cohomology/Dyadic/ArithFSM/ToBitFSM.lean)

```lean
theorem arithFSM2_signature_period_bound {n : Nat} (hn : 0 < n)
    (m : ArithFSM2 n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n)
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    fsm_signature_period_bound (m.toBitFSM hn) hnn
  refine ⟨N, P, hP, hbound, ?_⟩
  intro k hk_ge
  have h_pt : ∀ j, (m.toBitFSM hn).bits j = m.bits j := toBitFSM_bits_eq hn m
  have ⟨h_sig, _⟩ := hk k hk_ge
  -- h_sig : signature (m.toBitFSM hn).bits (k+P) = signature (m.toBitFSM hn).bits k
  -- Use pointwise equality
... [truncated]
```

## `pellFSMmod5_signature_period_bound` (E213/Math/Cohomology/Dyadic/ArithFSM/ToBitFSM.lean)

```lean
theorem pellFSMmod5_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 125
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod5.bits (k + P) = signature pellFSMmod5.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 5) (by decide) pellFSMmod5
  exact ⟨N, P, hP, hbound, hk⟩
```

## `arithFSM3_signature_period_bound` (E213/Math/Cohomology/Dyadic/ArithFSM/V3Bound.lean)

```lean
theorem arithFSM3_signature_period_bound {n : Nat} (hn : 0 < n)
    (m : ArithFSM3 n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n * n)
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k := by
  have hnnn : 0 < n * n * n := Nat.mul_pos (Nat.mul_pos hn hn) hn
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    fsm_signature_period_bound (ArithFSM3.toBitFSM hn m) hnnn
  refine ⟨N, P, hP, hbound, ?_⟩
  intro k hk_ge
  have h_pt : ∀ j, (ArithFSM3.toBitFSM hn m).bits j = m.bits j :=
    toBitFSM3_bits_eq hn m
  have ⟨h_sig, _⟩ := hk k hk_ge
  have h1 : signature (ArithFSM3.toBitFSM hn m).bits (k + P)
... [truncated]
```

## `tribFSMmod2_signature_period_bound` (E213/Math/Cohomology/Dyadic/ArithFSM/V3Bound.lean)

```lean
theorem tribFSMmod2_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 40
      ∧ ∀ k, k ≥ N →
        signature tribFSMmod2.bits (k + P) = signature tribFSMmod2.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM3_signature_period_bound (n := 2) (by decide) tribFSMmod2
  exact ⟨N, P, hP, hbound, hk⟩
```

## `aperiodic_bits_imp_not_ArithFSM3` (E213/Math/Cohomology/Dyadic/ArithFSM/V3Hardness.lean)

```lean
theorem aperiodic_bits_imp_not_ArithFSM3 (bs : Nat → Bool)
    (h_aperiodic : ∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) :
    ∀ (n : Nat) (hn : 0 < n) (m : ArithFSM3 n),
      ¬ (∀ k, m.bits k = bs k) := by
  intro n hn m h_match
  apply aperiodic_bits_imp_not_BitFSM bs h_aperiodic (n * n * n)
    (ArithFSM3.toBitFSM hn m)
  intro k
  rw [toBitFSM3_bits_eq hn m k]
  exact h_match k

/-- ★★★★★★ ArithFSM3-generable ⇒ eventually periodic. -/
```

## `ArithFSM3_generable_imp_eventually_periodic` (E213/Math/Cohomology/Dyadic/ArithFSM/V3Hardness.lean)

```lean
theorem ArithFSM3_generable_imp_eventually_periodic (bs : Nat → Bool) :
    (∃ (n : Nat) (hn : 0 < n) (m : ArithFSM3 n), ∀ k, m.bits k = bs k)
    → ∃ N P, 0 < P ∧ ∀ k, k ≥ N → bs (k + P) = bs k := by
  rintro ⟨n, hn, m, hmatch⟩
  apply BitFSM_generable_imp_eventually_periodic bs
  refine ⟨n * n * n, ArithFSM3.toBitFSM hn m, ?_⟩
  intro k
  rw [toBitFSM3_bits_eq hn m k]
  exact hmatch k
```

## `pellMod_periods_differ` (E213/Math/Cohomology/Dyadic/ArithFSM.lean)

```lean
theorem pellMod_periods_differ :
    (∃ p : Nat, p > 0 ∧ p = 3 ∧
      ∀ k, pellFSMmod2.bits (k + p) = pellFSMmod2.bits k)
    ∧ (∃ p : Nat, p > 0 ∧ p = 4 ∧
      ∀ k, pellFSMmod3.bits (k + p) = pellFSMmod3.bits k) :=
  ⟨⟨3, by decide, rfl, pellFSMmod2_bits_period_3⟩,
   ⟨4, by decide, rfl, pellFSMmod3_bits_period_4⟩⟩

/-- ★★ ArithFSM2 reduces to BitFSM(n²) via pair-encoding —
    same pigeonhole argument applies. -/
```

## `thueMorseAuto_witnesses_bitAuto2` (E213/Math/Cohomology/Dyadic/BitAuto2.lean)

```lean
theorem thueMorseAuto_witnesses_bitAuto2 :
    ∃ m : BitAuto2 2, ∀ k, k ≤ 7 → m.bits 4 k = thueMorse k := by
  refine ⟨thueMorseAuto, ?_⟩
  decide

/-- isPow2 indicator: 1 iff n is a power of 2 (popcount = 1).
    ∅-axiom: explicit Nat.lt proofs (Nat.succ_lt_succ chain). -/
```

## `fsm_joint_collision` (E213/Math/Cohomology/Dyadic/BitFSM/Bound.lean)

```lean
theorem fsm_joint_collision {n : Nat} (m : BitFSM n) (hn : 0 < n) :
    ∃ i, i ≤ 5 * n ∧ ∃ j, j ≤ 5 * n ∧ i < j
      ∧ signature m.bits i = signature m.bits j
      ∧ m.run i = m.run j := by
  have hlt : 5 * n < 5 * n + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (fsmJointAt m hn)
  have hval_eq : (fsmJointAt m hn ⟨i, hi⟩).val
                = (fsmJointAt m hn ⟨j, hj⟩).val :=
    collTest_imp_val_eq (fsmJointAt m hn) i j hi hj hcoll
  have hval : (signature m.bits i).val * n + (m.run i).val
              = (signature m.bits j).val * n + (m.run 
... [truncated]
```

## `fsm_signature_period_bound` (E213/Math/Cohomology/Dyadic/BitFSM/Bound.lean)

```lean
theorem fsm_signature_period_bound {n : Nat} (m : BitFSM n) (hn : 0 < n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * n
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k
      ∧ m.run (k + P) = m.run k := by
  obtain ⟨i, hi, j, hj, hij, hsig, hrun⟩ := fsm_joint_collision m hn
  have hP : 0 < j - i := sub_pos_of_lt_213 hij
  have hi_le_j : i ≤ j := Nat.le_of_lt hij
  have hbound : i + (j - i) ≤ 5 * n :=
    Nat.le_trans
      (Nat.le_of_eq (E213.Tactic.Nat213.add_sub_of_le hi_le_j)) hj
  refine ⟨i, j - i, hP, hbound, ?_⟩
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d :=
    ⟨k - i, (E213.
... [truncated]
```

## `tier0_equiv_bitfsm` (E213/Math/Cohomology/Dyadic/BitFSM/Converse.lean)

```lean
theorem tier0_equiv_bitfsm (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∃ (m : BitFSM p), ∀ k, m.bits k = bs k :=
  ⟨bitFSMOfPure bs p hp, bitFSMOfPure_correct bs p hp hbs⟩
```

## `tier0_bitfsm_witnesses` (E213/Math/Cohomology/Dyadic/BitFSM/Examples.lean)

```lean
theorem tier0_bitfsm_witnesses :
    (∃ m : BitFSM 2, m.bits 0 = false ∧ m.bits 1 = true)
    ∧ (∃ m : BitFSM 4, m.bits 2 = true ∧ m.bits 3 = true)
    ∧ (∃ m : BitFSM 3, m.bits 0 = false ∧ m.bits 2 = true) :=
  ⟨⟨fsm_one_third, by decide, by decide⟩,
   ⟨fsm_one_fifth, by decide, by decide⟩,
   ⟨fsm_one_seventh, by decide, by decide⟩⟩

/-- fsm_one_third's run state matches k % 2 (Nat-level). -/
```

## `fsm_run_collision` (E213/Math/Cohomology/Dyadic/BitFSM.lean)

```lean
theorem fsm_run_collision {n : Nat} (m : BitFSM n) :
    ∃ i, i ≤ n ∧ ∃ j, j ≤ n ∧ i < j ∧ m.run i = m.run j := by
  have hlt : n < n + 1 := Nat.lt_succ_self _
  let g : Fin (n+1) → Fin n := fun k => m.run k.val
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ := pigeonhole_collision hlt g
  refine ⟨i, Nat.lt_succ_iff.mp hi, j, Nat.lt_succ_iff.mp hj, hij, ?_⟩
  exact Fin.ext (collTest_imp_val_eq g i j hi hj hcoll)

/-- ∅-axiom replacement for `Nat.sub_pos_of_lt` (which leaks propext). -/
private theorem sub_pos_of_lt_213 : ∀ {a b : Nat}, a < b → 0 < b - a
  | 0, _, h => by rw [Nat.sub_zero]; exact h
  | _+
... [truncated]
```

## `fsm_run_eventually_periodic` (E213/Math/Cohomology/Dyadic/BitFSM.lean)

```lean
theorem fsm_run_eventually_periodic {n : Nat} (m : BitFSM n) :
    ∃ N P, 0 < P ∧ ∀ k, k ≥ N → m.run (k + P) = m.run k := by
  obtain ⟨i, _, j, _, hij, heq⟩ := fsm_run_collision m
  refine ⟨i, j - i, sub_pos_of_lt_213 hij, ?_⟩
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d :=
    ⟨k - i, (E213.Tactic.Nat213.add_sub_of_le hk).symm⟩
  clear hk
  have hij_eq : i + (j - i) = j :=
    E213.Tactic.Nat213.add_sub_of_le (Nat.le_of_lt hij)
  induction d with
  | zero =>
    show m.run (i + 0 + (j - i)) = m.run (i + 0)
    rw [Nat.add_zero, hij_eq]
    exact heq.symm
  | succ d' ih =>
    have h1 : i +
... [truncated]
```

## `fsm_bits_eventually_periodic` (E213/Math/Cohomology/Dyadic/BitFSM.lean)

```lean
theorem fsm_bits_eventually_periodic {n : Nat} (m : BitFSM n) :
    ∃ N P, 0 < P ∧ ∀ k, k ≥ N → m.bits (k + P) = m.bits k := by
  obtain ⟨N, P, hP, h⟩ := fsm_run_eventually_periodic m
  refine ⟨N, P, hP, ?_⟩
  intro k hk
  show m.out (m.run (k + P)) = m.out (m.run k)
  rw [h k hk]

/-- ★★★★★★ BitFSM-generated signature is eventually periodic. -/
```

## `fsm_signature_eventually_periodic` (E213/Math/Cohomology/Dyadic/BitFSM.lean)

```lean
theorem fsm_signature_eventually_periodic {n : Nat} (m : BitFSM n) :
    ∃ N P, 0 < P ∧ ∀ k, k ≥ N →
      signature m.bits (k + P) = signature m.bits k := by
  obtain ⟨N₀, P, hP, hbits⟩ := fsm_bits_eventually_periodic m
  exact signature_eventually_periodic_of_eventually_periodic_bits
    m.bits P N₀ hP (fun n hn => hbits n hn)
```

## `aperiodic_bits_imp_aperiodic_signature` (E213/Math/Cohomology/Dyadic/Classifier.lean)

```lean
theorem aperiodic_bits_imp_aperiodic_signature
    (bs : Nat → Bool)
    (h_aperiodic : ∀ p N : Nat, 0 < p →
                    ∃ n, n ≥ N ∧ bs (n + p) ≠ bs n) :
    ∀ p N : Nat, 0 < p →
      ¬ (∀ n, n ≥ N → signature bs (n + p) = signature bs n) := by
  intro p N hp h_sig_per
  obtain ⟨n, hn, hne⟩ := h_aperiodic p N hp
  exact hne (signature_periodic_implies_bits_periodic bs p N hp
              h_sig_per n hn)
```

## `sub_is_multiple_of_p` (E213/Math/Cohomology/Dyadic/ForwardClosure.lean)

```lean
theorem sub_is_multiple_of_p (i j p : Nat) (hp : 0 < p)
    (hij : i ≤ j) (hmod : i % p = j % p) :
    ∃ k, j - i = k * p := by
  refine ⟨(j - i) / p, ?_⟩
  have hjlt : j % p < p := Nat.mod_lt _ hp
  have hslt : (j - i) % p < p := Nat.mod_lt _ hp
  have h1 : (j - i) % p = 0 := by
    have hji : i + (j - i) = j := E213.Tactic.Nat213.add_sub_of_le hij
    have hadd : j % p = (i % p + (j - i)) % p := by
      have h := E213.Math.AddMod213.add_mod_left hp i (j - i)
      rw [hji] at h
      exact h
    rw [hmod] at hadd
    have hadd2 : (j % p + (j - i)) % p
                = (j % p % p + (j - i) 
... [truncated]
```

## `signature_eventually_periodic_of_periodic_bits` (E213/Math/Cohomology/Dyadic/ForwardClosure.lean)

```lean
theorem signature_eventually_periodic_of_periodic_bits
    (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N → signature bs (n + P) = signature bs n := by
  obtain ⟨i, _, j, _, hij, hsig, hmod⟩ := joint_state_collision bs p hp
  refine ⟨i, j - i, sub_pos_of_lt_213_local hij, ?_⟩
  obtain ⟨k, hk⟩ := sub_is_multiple_of_p i j p hp (Nat.le_of_lt hij) hmod
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = i + d :=
    ⟨n - i, (E213.Tactic.Nat213.add_sub_of_le hn).symm⟩
  clear hn
  have hij_le : i ≤ j := Nat.le_of_lt hij
  have hij_eq : i + (j - i) 
... [truncated]
```

## `joint_state_collision_at` (E213/Math/Cohomology/Dyadic/ForwardEventual.lean)

```lean
theorem joint_state_collision_at (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p) :
    ∃ i, i ≤ 5 * p ∧ ∃ j, j ≤ 5 * p ∧ i < j
      ∧ signature bs (N₀ + i) = signature bs (N₀ + j)
      ∧ i % p = j % p := by
  have hlt : 5 * p < 5 * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (jointStateAt bs p N₀ hp)
  have hval_eq : (jointStateAt bs p N₀ hp ⟨i, hi⟩).val
              = (jointStateAt bs p N₀ hp ⟨j, hj⟩).val :=
    collTest_imp_val_eq (jointStateAt bs p N₀ hp) i j hi hj hcoll
  have hval : (signature bs (N₀ + i)).val * p + i % p
              = 
... [truncated]
```

## `signature_eventually_periodic_of_eventually_periodic_bits` (E213/Math/Cohomology/Dyadic/ForwardEventual.lean)

```lean
theorem signature_eventually_periodic_of_eventually_periodic_bits
    (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p)
    (hbs : ∀ n, n ≥ N₀ → bs (n + p) = bs n) :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N → signature bs (n + P) = signature bs n := by
  obtain ⟨i, _, j, _, hij, hsig, hmod⟩ := joint_state_collision_at bs p N₀ hp
  refine ⟨N₀ + i, j - i, sub_pos_of_lt_213_local hij, ?_⟩
  obtain ⟨k, hk⟩ := sub_is_multiple_of_p i j p hp (Nat.le_of_lt hij) hmod
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = N₀ + i + d :=
    ⟨n - (N₀ + i), (E213.Tactic.Nat213.add_sub_of_le hn).symm⟩
  clear hn
  have hij_le : i ≤ j :=
... [truncated]
```

## `pigeonhole_collision` (E213/Math/Cohomology/Dyadic/ForwardPeriodicity.lean)

```lean
theorem pigeonhole_collision {N k : Nat} (h : N < k) (g : Fin k → Fin N) :
    ∃ i, i < k ∧ ∃ j, j < k ∧ i < j ∧ collisionTest g i j = true := by
  match searchOuter g k with
  | PSum.inl ⟨i, j, hik, hjk, hij, hcoll⟩ =>
    exact ⟨i, hik, j, hjk, hij, hcoll⟩
  | PSum.inr hno =>
    exfalso
    apply no_inj_lt h g
    intro x y hxy heq
    rcases Nat.lt_or_ge x.val y.val with hlt | hge
    · have hctf : collisionTest g x.val y.val = false :=
        hno x.val x.isLt y.val hlt y.isLt
      have hctt : collisionTest g x.val y.val = true :=
        g_eq_imp_collTest g x y heq
      exact Bool.noCo
... [truncated]
```

## `joint_state_collision` (E213/Math/Cohomology/Dyadic/ForwardPeriodicity.lean)

```lean
theorem joint_state_collision (bs : Nat → Bool) (p : Nat) (hp : 0 < p) :
    ∃ i, i ≤ 5 * p ∧ ∃ j, j ≤ 5 * p ∧ i < j
      ∧ signature bs i = signature bs j
      ∧ i % p = j % p := by
  have hlt : 5 * p < 5 * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (jointState bs p hp)
  have hi' : i ≤ 5 * p := Nat.lt_succ_iff.mp hi
  have hj' : j ≤ 5 * p := Nat.lt_succ_iff.mp hj
  have hval_eq : (jointState bs p hp ⟨i, hi⟩).val
                = (jointState bs p hp ⟨j, hj⟩).val :=
    collTest_imp_val_eq (jointState bs p hp) i j hi hj hcoll
  have hval 
... [truncated]
```

## `pellFSMmod2_signature_period_bound` (E213/Math/Cohomology/Dyadic/Pell/Bounds.lean)

```lean
theorem pellFSMmod2_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 20
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod2.bits (k + P) = signature pellFSMmod2.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 2) (by decide) pellFSMmod2
  exact ⟨N, P, hP, hbound, hk⟩

/-- ★★★★ Pell mod-3 signature period bound: 45 = 5·9. -/
```

## `pellFSMmod3_signature_period_bound` (E213/Math/Cohomology/Dyadic/Pell/Bounds.lean)

```lean
theorem pellFSMmod3_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 45
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod3.bits (k + P) = signature pellFSMmod3.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 3) (by decide) pellFSMmod3
  exact ⟨N, P, hP, hbound, hk⟩

/-- ★★★★★ Pell family bound table — GUARANTEE row (5n²). -/
```

## `pell_family_signature_period_bounds` (E213/Math/Cohomology/Dyadic/Pell/Bounds.lean)

```lean
theorem pell_family_signature_period_bounds :
    (∃ N P, 0 < P ∧ N + P ≤ 20
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod2.bits (k + P) = signature pellFSMmod2.bits k)
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 45
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod3.bits (k + P) = signature pellFSMmod3.bits k)
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 125
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod5.bits (k + P) = signature pellFSMmod5.bits k) :=
  ⟨pellFSMmod2_signature_period_bound,
   pellFSMmod3_signature_period_bound,
   pellFSMmod5_signature_period_bound⟩
```

## `pell_capstone` (E213/Math/Cohomology/Dyadic/Pell/Capstone.lean)

```lean
theorem pell_capstone :
    -- bit periodicity (mod 2, 3, 5)
    (∀ k, pellFSMmod2.bits (k + 3) = pellFSMmod2.bits k)
    ∧ (∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    -- concrete signature periodicity (mod 3, 5)
    ∧ (∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k)
    ∧ (∀ k, signature pellFSMmod5.bits (k + 10) = signature pellFSMmod5.bits k)
    -- mod 2 has signature period 6 from step 1
    ∧ (∀ k, k ≥ 1 →
        signature pellFSMmod2.bits (k + 6) = signature pellFSMmod2.bits k)
    -- Arith
... [truncated]
```

## `pell_family_closure` (E213/Math/Cohomology/Dyadic/Pell/Family.lean)

```lean
theorem pell_family_closure :
    -- bit periods
    (∀ k, pellFSMmod2.bits (k + 3) = pellFSMmod2.bits k)
    ∧ (∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + 8) = pellFSMmod7.bits k)
    -- TIGHT signature periods (mod 3, 5, 7 pure; mod 2 from step 1)
    ∧ (∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k)
    ∧ (∀ k, signature pellFSMmod5.bits (k + 10) = signature pellFSMmod5.bits k)
    ∧ (∀ k, signature pellFSMmod7.bits (k + 8) = signature pellFSMmod7.bits k)
    ∧ (∀ 
... [truncated]
```

## `thueMorse_aperiodic_short` (E213/Math/Cohomology/Dyadic/ThueMorse.lean)

```lean
theorem thueMorse_aperiodic_short :
    (∃ k, thueMorse (k + 1) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 2) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 3) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 4) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 5) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 6) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 7) ≠ thueMorse k)
    ∧ (∃ k, thueMorse (k + 8) ≠ thueMorse k) := by
  obtain ⟨h1, h2, h4, h7, h8⟩ := thueMorse_not_period_at_0
  obtain ⟨h3, h5, h6⟩ := thueMorse_not_period_3_5_6
  exact ⟨⟨0, h1⟩, ⟨0, h2⟩, ⟨2, h3⟩, ⟨0, h4⟩,
         ⟨1, h5⟩, ⟨4, h6⟩, ⟨0, h7⟩, ⟨0, h8⟩⟩
... [truncated]
```

## `aperiodic_bits_imp_not_BitFSM` (E213/Math/Cohomology/Dyadic/Tier2Hardness.lean)

```lean
theorem aperiodic_bits_imp_not_BitFSM (bs : Nat → Bool)
    (h_aperiodic : ∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) :
    ∀ (n : Nat) (m : BitFSM n), ¬ (∀ k, m.bits k = bs k) := by
  intro n m h_match
  obtain ⟨N, P, hP, h_per⟩ := fsm_bits_eventually_periodic m
  have h_bs_per : ∀ k, k ≥ N → bs (k + P) = bs k := by
    intro k hk
    rw [← h_match (k + P), ← h_match k]
    exact h_per k hk
  obtain ⟨k, hk, hne⟩ := h_aperiodic N P hP
  exact hne (h_bs_per k hk)

/-- Convenience: aperiodic ⇒ ∀ n, no BitFSM(n). -/
```

## `aperiodic_bits_imp_no_BitFSM` (E213/Math/Cohomology/Dyadic/Tier2Hardness.lean)

```lean
theorem aperiodic_bits_imp_no_BitFSM (bs : Nat → Bool)
    (h_aperiodic : ∀ N P, 0 < P → ∃ k, k ≥ N ∧ bs (k + P) ≠ bs k) :
    ¬ ∃ (n : Nat) (m : BitFSM n), ∀ k, m.bits k = bs k := by
  rintro ⟨n, m, hmatch⟩
  exact aperiodic_bits_imp_not_BitFSM bs h_aperiodic n m hmatch

/-- ★★★★★★ BitFSM-generable ⇒ eventually periodic.  The forward
    direction of the BitFSM-class characterisation.  (The
    converse for genuinely eventually-periodic-with-pre-period
    requires a pre-period BitFSM construction; for purely
    periodic case see `tier0_equiv_bitfsm`.) -/
```

## `BitFSM_generable_imp_eventually_periodic` (E213/Math/Cohomology/Dyadic/Tier2Hardness.lean)

```lean
theorem BitFSM_generable_imp_eventually_periodic (bs : Nat → Bool) :
    (∃ (n : Nat) (m : BitFSM n), ∀ k, m.bits k = bs k)
    → ∃ N P, 0 < P ∧ ∀ k, k ≥ N → bs (k + P) = bs k := by
  rintro ⟨n, m, hmatch⟩
  obtain ⟨N, P, hP, h_per⟩ := fsm_bits_eventually_periodic m
  refine ⟨N, P, hP, ?_⟩
  intro k hk
  rw [← hmatch (k + P), ← hmatch k]
  exact h_per k hk
```

## `aperiodic_bits_imp_aperiodic_sig` (E213/Math/Cohomology/Dyadic/TierBridge.lean)

```lean
theorem aperiodic_bits_imp_aperiodic_sig
    (bs : Nat → Bool)
    (h : ∀ p N : Nat, 0 < p → ∃ n, n ≥ N ∧ bs (n + p) ≠ bs n)
    (p : Nat) :
    ¬ EventuallyPeriodic (signature bs) p := by
  rintro ⟨hp, N, hN⟩
  obtain ⟨n, hn, hne⟩ := h p N hp
  exact hne (signature_periodic_implies_bits_periodic bs p N hp hN n hn)
```

## `tribonacci_capstone` (E213/Math/Cohomology/Dyadic/Trib/Capstone.lean)

```lean
theorem tribonacci_capstone :
    -- bit periodicity
    (∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k)
    -- concrete signature periodicity (pre-period 1)
    ∧ (∀ k, k ≥ 1 →
        signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k)
    -- ArithFSM3(n) ⊂ BitFSM(n³) bit-stream equivalence
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) (k : Nat),
        (ArithFSM3.toBitFSM hn m).bits k = m.bits k)
    -- ArithFSM3(n) signature period ≤ 5n³
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM3 n),
        ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n * n)
          ∧ ∀ k, k ≥ N → signat
... [truncated]
```

## `exists_pattern_213` (E213/Math/Cohomology/HodgeConjecture/Bridge/G7Vacuity.lean)

```lean
theorem exists_pattern_213 :
    ∃ n : Nat, isExoticPattern n = true ∧ n < 32 :=
  ⟨witness_213, by decide, by decide⟩
```

## `g7_phase_1_pure_capstone` (E213/Math/Cohomology/HodgeConjecture/Bridge/G7Vacuity.lean)

```lean
theorem g7_phase_1_pure_capstone :
    witness_213 = 3
    ∧ isExoticPattern witness_213 = true
    ∧ witness_213 < 32
    ∧ (∃ n : Nat, isExoticPattern n = true ∧ n < 32) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨3, by decide, by decide⟩
```

## `exists_213_constructive` (E213/Math/Cohomology/HodgeConjecture/Bridge/G9ReductioVoid.lean)

```lean
theorem exists_213_constructive : ∃ n : Nat, P_demo n = true :=
  ⟨3, rfl⟩
```

## `exists_classical_reductio` (E213/Math/Cohomology/HodgeConjecture/Bridge/G9ReductioVoid.lean)

```lean
theorem exists_classical_reductio :
    (¬∀ n : Nat, ¬(P_demo n = true)) → ∃ n : Nat, P_demo n = true :=
  fun h => Classical.byContradiction
    (fun hne => h (fun n hp => hne ⟨n, hp⟩))
```

## `reductio_existence_universal` (E213/Math/Cohomology/HodgeConjecture/Bridge/G9ReductioVoid.lean)

```lean
theorem reductio_existence_universal {α : Type} (P : α → Prop)
    (h : ¬∀ x, ¬P x) : ∃ x, P x :=
  Classical.byContradiction
    (fun hne => h (fun x hp => hne ⟨x, hp⟩))
```

## `g9_capstone_pure` (E213/Math/Cohomology/HodgeConjecture/Bridge/G9ReductioVoid.lean)

```lean
theorem g9_capstone_pure :
    P_demo 3 = true
    ∧ (∃ n : Nat, P_demo n = true)
    ∧ (3 : Nat) = 3
    ∧ ¬((3 : Nat) < 3) := by
  refine ⟨rfl, ⟨3, rfl⟩, rfl, ?_⟩
  decide
```

## `f9Lens_not_collapse` (E213/Math/Diagonal/Classification.lean)

```lean
theorem f9Lens_not_collapse : ¬ ∃ e : F9, Collapse f9Lens e := by
  intro ⟨e, hC⟩
  have h1 : F9.mul F9.one F9.one = e := hC F9.one
  have h2 : F9.mul F9.i F9.i = e := hC F9.i
  have hne : F9.mul F9.one F9.one ≠ F9.mul F9.i F9.i := by decide
  exact hne (h1.trans h2.symm)
```

## `signedLens_image_le_zero` (E213/Math/Infinity/BTower.lean)

```lean
theorem signedLens_image_le_zero :
    ∀ z : Int, z ≤ 0 → ∃ r : Raw, signedLens.view r = z := by
  intro z hz
  have ⟨n, hn⟩ : ∃ n : Nat, z = -(n : Int) := by
    refine ⟨(-z).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; omega
  refine ⟨rawBTower n, ?_⟩
  rw [rawBTower_signed, hn]

/-- **signedLens is surjective onto `ℤ`.**  For every integer
    `z`, either `z ≥ -1` (use `rawTower`) or `z ≤ 0` (use
    `rawBTower`).  The two cases overlap at `z ∈ {-1, 0}`
    which is fine for surjectivity. -/
```

## `signedLens_unbounded_below` (E213/Math/Infinity/BTower.lean)

```lean
theorem signedLens_unbounded_below :
    ∀ N : Nat, ∃ r : Raw, signedLens.view r ≤ -(N : Int) := by
  intro N
  obtain ⟨r, hr⟩ := signedLens_image_le_zero (-(N : Int)) (by omega)
  exact ⟨r, by rw [hr]; exact Int.le_refl _⟩
```

## `boolSpace_at_least_countable` (E213/Math/Infinity/BoolSpace.lean)

```lean
theorem boolSpace_at_least_countable :
    ∃ f : Nat → (Raw → Bool), Function.Injective f :=
  ⟨nToRawBool, nToRawBool_injective⟩

/-- **Strict cardinality gap.**  There is an injection ℕ →
    (Raw → Bool) *and* no surjection Raw → (Raw → Bool).
    Combined with Σ3 (Raw ≥ ℕ), this establishes that
    the function space is strictly larger than Raw as a
    Cantor-style cardinality relation. -/
```

## `cantor_gap_witnessed` (E213/Math/Infinity/BoolSpace.lean)

```lean
theorem cantor_gap_witnessed :
    (∃ f : Nat → (Raw → Bool), Function.Injective f)
      ∧ (¬ ∃ h : Raw → (Raw → Bool), Function.Surjective h) :=
  ⟨boolSpace_at_least_countable, cantor_raw_bool⟩
```

## `cantor_general` (E213/Math/Infinity/Cantor.lean)

```lean
theorem cantor_general {X : Type} :
    ¬ ∃ f : X → (X → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  let g : X → Bool := fun x => ! (f x x)
  obtain ⟨k, hk⟩ := hf g
  have hpoint : f k k = g k := congrFun hk k
  have hflip  : g k = ! (f k k) := rfl
  have hcontra : f k k = ! (f k k) := hpoint.trans hflip
  cases h : f k k
  · rw [h] at hcontra; exact Bool.noConfusion hcontra
  · rw [h] at hcontra; exact Bool.noConfusion hcontra

/-- **Σ5 — Cantor on Raw.** -/
```

## `cantor_raw_bool` (E213/Math/Infinity/Cantor.lean)

```lean
theorem cantor_raw_bool :
    ¬ ∃ f : Raw → (Raw → Bool), Function.Surjective f :=
  cantor_general
```

## `chain_uncountable` (E213/Math/Infinity/Chain.lean)

```lean
theorem chain_uncountable :
    ¬ ∃ f : Nat → (Nat → Raw), Function.Surjective f := by
  rintro ⟨f, hf⟩
  let g : Nat → Raw :=
    fun n => if f n n = Raw.a then Raw.b else Raw.a
  obtain ⟨k, hk⟩ := hf g
  have hpoint : f k k = g k := congrFun hk k
  by_cases hval : f k k = Raw.a
  · have hg : g k = Raw.b := by
      show (if f k k = Raw.a then Raw.b else Raw.a) = Raw.b
      rw [if_pos hval]
    rw [hg, hval] at hpoint
    exact absurd hpoint (by decide)
  · have hg : g k = Raw.a := by
      show (if f k k = Raw.a then Raw.b else Raw.a) = Raw.a
      rw [if_neg hval]
    rw [hg] at hpoint
   
... [truncated]
```

## `raw_at_least_countable` (E213/Math/Infinity/Countable.lean)

```lean
theorem raw_at_least_countable :
    ∃ f : Nat → Raw, Function.Injective f :=
  ⟨rawTower, rawTower_injective⟩
```

## `raw_at_most_countable` (E213/Math/Infinity/Godel.lean)

```lean
theorem raw_at_most_countable :
    ∃ f : Raw → Nat, Function.Injective f :=
  ⟨Raw.toNat, Raw.toNat_injective⟩
```

## `raw_equipotent_nat` (E213/Math/Infinity/Godel.lean)

```lean
theorem raw_equipotent_nat :
    (∃ f : Nat → Raw, Function.Injective f)
      ∧ (∃ g : Raw → Nat, Function.Injective g) :=
  ⟨raw_at_least_countable, raw_at_most_countable⟩
```

## `leaves_surjective_pos` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem leaves_surjective_pos :
    ∀ n : Nat, 1 ≤ n → ∃ r : Raw, Lens.leaves.view r = n := by
  intro n hn
  have ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
    have h := E213.Tactic.Nat213.add_sub_of_le hn
    rw [Nat.add_comm 1 (n - 1)] at h
    exact h.symm⟩
  refine ⟨rawTower m, ?_⟩
  show Raw.fold 1 1 (· + ·) (rawTower m) = n
  rw [Raw.fold_eq_leaves, rawTower_leaves, hm]
```

## `depth_surjective` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem depth_surjective :
    ∀ n : Nat, ∃ r : Raw, Lens.depth.view r = n := by
  intro n
  refine ⟨rawTower n, ?_⟩
  show Raw.fold 0 0 (fun a b => 1 + Nat.max a b) (rawTower n) = n
  rw [Raw.fold_eq_depth]
  exact treeTower_depth n
```

## `parityLens_image_true` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem parityLens_image_true : ∃ r : Raw, parityLens.view r = true :=
  ⟨Raw.a, rfl⟩
```

## `parityLens_image_false` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem parityLens_image_false : ∃ r : Raw, parityLens.view r = false :=
  ⟨parityLens_sample_even, parityLens_sample_even_view⟩

/-- **`maxLens` image covers both 0 and 1.** -/
```

## `maxLens_image_zero` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem maxLens_image_zero : ∃ r : Raw, maxLens.view r = 0 :=
  ⟨Raw.a, rfl⟩
```

## `maxLens_image_one` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem maxLens_image_one : ∃ r : Raw, maxLens.view r = 1 :=
  ⟨Raw.b, rfl⟩

/-- **`maxLens` image is contained in `{0, 1}`.**  Since base
    values are 0,1 and `max` preserves this set. -/
```

## `signedLens_image_ge_neg_one` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem signedLens_image_ge_neg_one :
    ∀ z : Int, -1 ≤ z → ∃ r : Raw, signedLens.view r = z := by
  intro z hz
  have ⟨n, hn⟩ : ∃ n : Nat, z = (n : Int) - 1 := by
    refine ⟨(z + 1).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  refine ⟨rawTower n, ?_⟩
  show Raw.fold (1 : Int) (-1) (· + ·) (rawTower n) = z
  rw [hn]
  exact treeTower_signed n

/-- **signedLens image is unbounded above.**  For every
    `N : ℕ`, some Raw term has signed view `≥ N`. -/
```

## `signedLens_unbounded_above` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem signedLens_unbounded_above :
    ∀ N : Nat, ∃ r : Raw, (N : Int) ≤ signedLens.view r := by
  intro N
  obtain ⟨r, hr⟩ := signedLens_image_ge_neg_one (N : Int) (by omega)
  exact ⟨r, by rw [hr]; exact Int.le_refl _⟩
```

## `sigma7_cardinality_is_lens_output` (E213/Math/Infinity/LensCardinality.lean)

```lean
theorem sigma7_cardinality_is_lens_output :
    (∃ g : Raw → Nat, Function.Injective g)
      ∧ (∃ f : Nat → Raw, Function.Injective f)
      ∧ (¬ ∃ h : Raw → (Raw → Bool), Function.Surjective h)
      ∧ (∀ X : Type, ¬ ∃ k : X → (X → Bool), Function.Surjective k) := by
  refine ⟨raw_at_most_countable, raw_at_least_countable,
          cantor_raw_bool, ?_⟩
  intro _; exact cantor_general
```

## `tower_0_1` (E213/Math/Infinity/Tower.lean)

```lean
theorem tower_0_1 : ¬ ∃ f : Raw → L1, Function.Surjective f :=
  cantor_general

/-- **Layer 1 → Layer 2**: no surjection `(Raw → Bool) →
    ((Raw → Bool) → Bool)`.  Cantor's ladder second rung. -/
```

## `tower_1_2` (E213/Math/Infinity/Tower.lean)

```lean
theorem tower_1_2 : ¬ ∃ f : L1 → L2, Function.Surjective f :=
  cantor_general

/-- **Layer 2 → Layer 3**: third rung. -/
```

## `tower_2_3` (E213/Math/Infinity/Tower.lean)

```lean
theorem tower_2_3 : ¬ ∃ f : L2 → L3, Function.Surjective f :=
  cantor_general
```

## `tower_3_4` (E213/Math/Infinity/Tower.lean)

```lean
theorem tower_3_4 : ¬ ∃ f : L3 → L4, Function.Surjective f :=
  cantor_general

/-- **Layer 4 → Layer 5**: fifth rung. -/
```

## `tower_4_5` (E213/Math/Infinity/Tower.lean)

```lean
theorem tower_4_5 : ¬ ∃ f : L4 → L5, Function.Surjective f :=
  cantor_general

/-- **Generic recursion**: the Cantor tower is unbounded.
    For every `X : Type`, the function space `X → Bool`
    has no surjection from `X`.  Since each layer
    `L(k+1) = L(k) → Bool`, this iterates indefinitely. -/
```

## `tower_unbounded` (E213/Math/Infinity/Tower.lean)

```lean
theorem tower_unbounded {X : Type} :
    ¬ ∃ f : X → (X → Bool), Function.Surjective f :=
  cantor_general
```

## `even_split` (E213/Math/Irrational/Sqrt2Pure.lean)

```lean
theorem even_split (m : Nat) (h : isEven m = true) : ∃ m', m = 2 * m' := by
  cases nat_dichotomy m with
  | inl h' => exact h'
  | inr h' =>
      obtain ⟨k, hk⟩ := h'
      exfalso
      rw [hk, isEven_two_mul_succ] at h
      exact Bool.noConfusion h

/-- Descent: m = 2*m' and m^2 = 2*(k*k) → 2*(m'*m') = k*k. -/
```

## `three_split` (E213/Math/Irrational/Sqrt3Pure.lean)

```lean
theorem three_split (m : Nat) (h : mod3 m = 0) : ∃ m', m = 3 * m' := by
  cases nat_trichotomy m with
  | inl h' => exact h'
  | inr h' =>
      cases h' with
      | inl h'' =>
          obtain ⟨k, hk⟩ := h''
          exfalso; rw [hk, mod3_three_mul_one] at h
          exact Nat.noConfusion h
      | inr h'' =>
          obtain ⟨k, hk⟩ := h''
          exfalso; rw [hk, mod3_three_mul_two] at h
          exact Nat.noConfusion h

/-- Descent step: m = 3*m', m^2 = 3*(k*k) → 3*(m'*m') = k*k. -/
```

## `five_split` (E213/Math/Irrational/Sqrt5Pure.lean)

```lean
theorem five_split (m : Nat) (h : mod5 m = 0) : ∃ m', m = 5 * m' := by
  rcases nat_quintichotomy m with h' | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact h'
  · exfalso; rw [hk, mod5_five_mul_one] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_two] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_three] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_four] at h; exact Nat.noConfusion h
```

## `nat_trichotomy` (E213/Math/ModArith/PureNatMod3.lean)

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
      | inr h =>
          cases h with
          | inl h' =>
              obtain ⟨k, hk⟩ := h'
              right; right
              exact ⟨k, by rw [hk]⟩
          | inr h' =>
              obtain ⟨k, hk⟩ := h'
              left
              exact ⟨k + 1, by rw [hk, Nat.mul_succ]⟩
```

## `nat_quintichotomy` (E213/Math/ModArith/PureNatMod5.lean)

```lean
theorem nat_quintichotomy (n : Nat) :
    (∃ k, n = 5 * k) ∨ (∃ k, n = 5 * k + 1) ∨ (∃ k, n = 5 * k + 2) ∨
    (∃ k, n = 5 * k + 3) ∨ (∃ k, n = 5 * k + 4) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m ih =>
      rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
      · exact Or.inr (Or.inl ⟨k, by rw [hk]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, by rw [hk]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by rw [hk]⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, by rw [hk]⟩)))
      · exact Or.inl ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

/-- (5k)^2 = 5·
... [truncated]
```

## `sqrt4_rational` (E213/Math/PrimeDescentObservations.lean)

```lean
theorem sqrt4_rational : ∃ m k : Nat, k ≥ 1 ∧ m * m = 4 * (k * k) :=
  ⟨2, 1, Nat.le_refl 1, rfl⟩

/-- **Direct implication of Observation 1**: the descent template
    *cannot* work for sqrt4 — if it did, contradiction (rational
    solution exists). -/
```

## `sqrt16_rational` (E213/Math/PrimeDescentObservations.lean)

```lean
theorem sqrt16_rational : ∃ m k : Nat, k ≥ 1 ∧ m * m = 16 * (k * k) :=
  ⟨4, 1, Nat.le_refl 1, rfl⟩
```

## `nat_dichotomy` (E213/Math/PureNat.lean)

```lean
theorem nat_dichotomy (m : Nat) :
    (∃ k, m = 2 * k) ∨ (∃ k, m = 2 * k + 1) := by
  induction m with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
      cases ih with
      | inl h =>
          obtain ⟨k, hk⟩ := h
          right
          exact ⟨k, by rw [hk]⟩
      | inr h =>
          obtain ⟨k, hk⟩ := h
          left
          exact ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

/-- Even squared: `(2k)^2 = 2*(2*(k*k))`. -/
```

## `antiderivative_capstone` (E213/Math/Real213/Antiderivative.lean)

```lean
theorem antiderivative_capstone (c : Nat → Nat → Bool) :
    -- (1) id is antiderivative of constant 1
    idIsDifferentiable.derivative = constCutFn (constCut 1 1)
    -- (2) constant c is antiderivative of constant 0
    ∧ (constIsDifferentiable c).derivative = constCutFn (constCut 0 1)
    -- (3) Class non-empty: examples exist
    ∧ ∃ F sF f, IsAntiderivative F sF f :=
  ⟨rfl, rfl,
   ⟨id, idIsDifferentiable, constCutFn (constCut 1 1),
    IsAntiderivative.id_anti⟩⟩
```

## `dyadic_bracket_eventually_fits` (E213/Math/Real213/BracketCauchyModulus.lean)

```lean
theorem dyadic_bracket_eventually_fits (L E m k : Nat) (hm : 1 ≤ m) :
    ∃ N, ∀ n ≥ N, dyadicCut L (E + n) m k = true :=
  ⟨L * k, fun n hn => dyadic_bracket_cauchy_modulus L E m k hm n hn⟩
```

## `cutMulInner_eq_true_iff` (E213/Math/Real213/CutMulComm.lean)

```lean
theorem cutMulInner_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m1 : Nat) (n : Nat) :
    cutMulInner cx cy k m m1 n = true ↔
    ∃ m2, m2 ≤ n ∧ cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k := by
  induction n with
  | zero =>
    constructor
    · intro h
      have h' : (cx m1 k && cy 0 k && decide (m1 * 0 ≤ m * k)) = true := h
      refine ⟨0, Nat.le_refl _, ?_, ?_, ?_⟩
      · cases hcx : cx m1 k with
        | true => rfl
        | false => rw [hcx] at h'; cases h'
      · cases hcy : cy 0 k with
        | true => rfl
        | false =>
          cases hcx : cx m1 k <;> rw [hcx, 
... [truncated]
```

## `cutMulOuter_eq_true_iff` (E213/Math/Real213/CutMulComm.lean)

```lean
theorem cutMulOuter_eq_true_iff (cx cy : Nat → Nat → Bool)
    (k m m2Bound : Nat) :
    ∀ n, cutMulOuter cx cy k m m2Bound n = true ↔
    ∃ m1, m1 ≤ n ∧ ∃ m2, m2 ≤ m2Bound ∧
      cx m1 k = true ∧ cy m2 k = true ∧ m1 * m2 ≤ m * k
  | 0 => by
    constructor
    · intro h
      have h_inner : cutMulInner cx cy k m 0 m2Bound = true := h
      obtain ⟨m2, hm2, hcx, hcy, hmul⟩ :=
        (cutMulInner_eq_true_iff cx cy k m 0 m2Bound).mp h_inner
      exact ⟨0, Nat.le_refl _, m2, hm2, hcx, hcy, hmul⟩
    · rintro ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩
      have hm1_zero : m1 = 0 := Nat.le_zero.mp hm1

... [truncated]
```

## `cutSumAux_eq_true_iff` (E213/Math/Real213/CutSumComm.lean)

```lean
theorem cutSumAux_eq_true_iff (cx cy : Nat → Nat → Bool) (k M : Nat) (n : Nat) :
    cutSumAux cx cy k M n = true ↔
    ∃ i, i ≤ n ∧ cx i (2*k) = true ∧ cy (M - i) (2*k) = true := by
  induction n with
  | zero =>
    constructor
    · intro h
      refine ⟨0, Nat.le_refl _, ?_, ?_⟩
      · cases hcx : cx 0 (2*k) with
        | true => rfl
        | false =>
          have : (cx 0 (2*k) && cy M (2*k)) = true := h
          rw [hcx] at this; cases this
      · rw [Nat.sub_zero]
        cases hcy : cy M (2*k) with
        | true => rfl
        | false =>
          have : (cx 0 (2*k) && cy M (2*k
... [truncated]
```

## `no_pi_in_finite_riemann` (E213/Math/Real213/DyadicRiemann.lean)

```lean
theorem no_pi_in_finite_riemann (a b : Nat) (db : DyadicBracket) (n : Nat) :
    ∃ M : Nat, cutEq (riemannSampleSum (constCutFn (constCut a b)) db n)
                     (constCut M b) :=
  ⟨2^n * a, riemannSampleSum_constCut_at a b db n⟩
```

## `consistent_oracle_existence_witnesses` (E213/Math/Real213/DyadicTrajectory.lean)

```lean
theorem consistent_oracle_existence_witnesses :
    -- (1) Any oracle on collapsed bracket: ConsistentOracle exists.
    (∀ db : DyadicBracket, db.numA = db.numB →
      ∀ oracle : DyadicOracle,
      ∃ co : ConsistentOracle db, co.oracle = oracle)
    -- (2) alwaysTrue on unit: ConsistentOracle exists.
    ∧ (∃ co : ConsistentOracle unitBracket, co.oracle = alwaysTrue)
    -- (3) alwaysFalse on unit: ConsistentOracle exists.
    ∧ (∃ co : ConsistentOracle unitBracket, co.oracle = alwaysFalse) :=
  ⟨fun db h oracle => ⟨ConsistentOracle.collapsed db h oracle, rfl⟩,
   ⟨ConsistentOracle.alwaysTr
... [truncated]
```

## `mid_id_square_has_dyadic_witness` (E213/Math/Real213/FluxMVTMore.lean)

```lean
theorem mid_id_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
            ).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.mid_id_square

/-- Phase BU capstone: 2 functions with constructive dyadic MVT witnesses. -/
```

## `mvt_witness_extended_capstone` (E213/Math/Real213/FluxMVTMore.lean)

```lean
theorem mvt_witness_extended_capstone :
    squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) = constCut 1 1
    ∧ (∃ c, squareIsDifferentiable.derivative c = constCut 1 1)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative c = constCut 1 1) :=
  ⟨squareDerivative_at_half,
   mid_id_square_derivative_at_half,
   square_has_dyadic_witness,
   mid_id_square_has_dyadic_witness⟩
```

## `mid_id_mid_id_square_has_dyadic_witness` (E213/Math/Real213/FluxMVTNested.lean)

```lean
theorem mid_id_mid_id_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable idIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              )).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.mid_id_mid_id_square

/-- Phase CF capstone: nested mid witness chain. -/
```

## `nested_mid_witness_capstone` (E213/Math/Real213/FluxMVTNested.lean)

```lean
theorem nested_mid_witness_capstone :
    -- (1) explicit witness
    (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) = constCut 1 1
    -- (2) MVT existence (constructive)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                )).derivative c = constCut 1 1) :=
  ⟨mid_id_mid_id_square_derivative_at_half,
   mid_id_mid_id_square_has_dyadic_witness⟩
```

## `mid_mid_id_square_square_has_dyadic_witness` (E213/Math/Real213/FluxMVTNested2.lean)

```lean
theorem mid_mid_id_square_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            squareIsDifferentiable).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists
    HasDyadicMVTWitness.mid_mid_id_square_square

/-- Phase CJ capstone. -/
```

## `mid_mid_id_square_square_capstone` (E213/Math/Real213/FluxMVTNested2.lean)

```lean
theorem mid_mid_id_square_square_capstone :
    (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2)
        = constCut 1 1
    ∧ (∃ c, (midIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
              squareIsDifferentiable).derivative c = constCut 1 1) :=
  ⟨mid_mid_id_square_square_derivative_at_half,
   mid_mid_id_square_square_has_dyadic_witness⟩
```

## `dyadic_witness_existential_capstone` (E213/Math/Real213/FluxMVTPattern.lean)

```lean
theorem dyadic_witness_existential_capstone :
    (∃ c, idIsDifferentiable.derivative c = constCut 1 1)
    ∧ (∃ c, squareIsDifferentiable.derivative c = constCut 1 1)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative c = constCut 1 1)
    ∧ (∃ c, (composeIsDifferentiable squareIsDifferentiable
              idIsDifferentiable).derivative c = constCut 1 1)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                )).derivative c = constCut 1 1) :=
  ⟨⟨const
... [truncated]
```

## `mvt_square_explicit_witness` (E213/Math/Real213/FluxMVTWitness.lean)

```lean
theorem mvt_square_explicit_witness :
    ∃ c, squareIsDifferentiable.derivative c = constCut 1 1 :=
  ⟨constCut 1 2, squareDerivative_at_half⟩

/-- The witness c = 1/2 is interior to [0, 1]: it equals constCut 1 2. -/
```

## `mvt_square_with_witness_capstone` (E213/Math/Real213/FluxMVTWitness.lean)

```lean
theorem mvt_square_with_witness_capstone :
    localDivergence (fun x => cutMul x x) unitBracket
       = ofCut (constCut 1 1)
    ∧ squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    ∧ ∃ c, squareIsDifferentiable.derivative c = constCut 1 1 :=
  ⟨mvt_square_unitBracket, squareDerivative_at_half,
   ⟨constCut 1 2, squareDerivative_at_half⟩⟩
```

## `mvt_exists` (E213/Math/Real213/HasDyadicMVTWitness.lean)

```lean
theorem mvt_exists {f sf} (w : @HasDyadicMVTWitness f sf) :
    ∃ c, sf.derivative c = constCut 1 1 :=
  ⟨w.witness, w.proof⟩
```

## `square_has_dyadic_witness` (E213/Math/Real213/HasDyadicMVTWitness.lean)

```lean
theorem square_has_dyadic_witness :
    ∃ c, squareIsDifferentiable.derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.square

/-- The witness for x² is exactly 1/2 (≥ 0 and ≤ 1). -/
```

## `mvt_witness_capstone` (E213/Math/Real213/HasDyadicMVTWitness.lean)

```lean
theorem mvt_witness_capstone :
    HasDyadicMVTWitness.square.witness = constCut 1 2
    ∧ squareIsDifferentiable.derivative HasDyadicMVTWitness.square.witness
       = constCut 1 1
    ∧ ∃ c, squareIsDifferentiable.derivative c = constCut 1 1:=
  ⟨rfl, HasDyadicMVTWitness.square.proof, square_has_dyadic_witness⟩
```

## `id_compose_square_has_dyadic_witness` (E213/Math/Real213/MVTWitnessChain.lean)

```lean
theorem id_compose_square_has_dyadic_witness :
    ∃ c, (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
            ).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.id_compose_square

/-- Phase BW capstone: chain-rule MVT witness for id ∘ x². -/
```

## `chain_rule_witness_capstone` (E213/Math/Real213/MVTWitnessChain.lean)

```lean
theorem chain_rule_witness_capstone :
    (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable).derivative
        (constCut 1 2) = constCut 1 1
    ∧ (∃ c, (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
              ).derivative c = constCut 1 1) :=
  ⟨id_compose_square_derivative_at_half,
   id_compose_square_has_dyadic_witness⟩
```

## `phaseBX_witness_capstone` (E213/Math/Real213/PhaseBXCapstone.lean)

```lean
theorem phaseBX_witness_capstone (c : Nat → Nat → Bool) :
    -- (BT) HasDyadicMVTWitness for x²
    squareIsDifferentiable.derivative
        square.witness = constCut 1 1
    -- (BU) HasDyadicMVTWitness for mid(x, x²)
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative mid_id_square.witness = constCut 1 1
    -- (BV) id at c = 0
    ∧ idIsDifferentiable.derivative (constCut 0 1) = constCut 1 1
    -- (BV) id at c = 1
    ∧ idIsDifferentiable.derivative (constCut 1 1) = constCut 1 1
    -- (BV) id at any c
    ∧ idIsDifferentiable.derivative c = constCut 
... [truncated]
```

## `phaseCM_final_capstone` (E213/Math/Real213/PhaseCMFinalCapstone.lean)

```lean
theorem phaseCM_final_capstone (n : Nat)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1)
    (h_right : f (constCut 1 1) = constCut 1 1) :
    -- (BE) generic ∀n cutPow MVT
    localDivergence (fun x => cutPow x (n+1)) unitBracket
       = ofCut (constCut 1 1)
    -- (BF) general passthrough MVT
    ∧ localDivergence f unitBracket
       = ofCut (constCut 1 1)
    -- (BR) explicit dyadic witness for x²
    ∧ squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    -- (BU/BR) mid(x, x²) witness
    ∧ (midIsDifferentiable idIsDifferenti
... [truncated]
```

## `riemann_const_finite_rational` (E213/Math/Real213/PhaseJCapstone.lean)

```lean
theorem riemann_const_finite_rational
    (a b : Nat) (db : DyadicBracket) (n : Nat) :
    ∃ M : Nat, ∀ m k, riemannSampleSum (constCutFn (constCut a b)) db n m k
                    = constCut M b m k :=
  ⟨2^n * a, riemannSampleSum_constCut_at a b db n⟩

/-- **Phase J no-infinity capstone**: π / ∞ / classical limits all
    structurally absent from the dyadic apparatus.  All concrete
    quantities are explicit Nat rationals.  Pointwise — strict ∅-axiom. -/
```

## `phaseJ_no_infinity` (E213/Math/Real213/PhaseJCapstone.lean)

```lean
theorem phaseJ_no_infinity (db : DyadicBracket) (oracle : DyadicOracle)
    (n : Nat) (a b : Nat) :
    (DyadicBracket.bisectN oracle n db).leftCut
    = dyadicCut (DyadicBracket.bisectN oracle n db).numA
                (DyadicBracket.bisectN oracle n db).expE
    ∧ (DyadicBracket.bisectN oracle n db).rightCut
    = dyadicCut (DyadicBracket.bisectN oracle n db).numB
                (DyadicBracket.bisectN oracle n db).expE
    -- Riemann constant gives finite rational closed form (pointwise).
    ∧ ∃ M, ∀ m k, riemannSampleSum (constCutFn (constCut a b)) db n m k
                = constCut M b
... [truncated]
```

## `consistentOracle_exists_on_collapsed` (E213/Math/Real213/PhaseJCapstone.lean)

```lean
theorem consistentOracle_exists_on_collapsed
    (db : DyadicBracket) (h : db.numA = db.numB)
    (oracle : DyadicOracle) :
    ∃ co : ConsistentOracle db, co.oracle = oracle :=
  ⟨ConsistentOracle.collapsed db h oracle, rfl⟩
```

## `phaseL_unified_capstone` (E213/Math/Real213/PhaseLCapstone.lean)

```lean
theorem phaseL_unified_capstone (n : Nat) (a b : Nat) :
    -- (I) alwaysTrue trajectory: bracket (0, 1, n)
    (DyadicBracket.bisectN alwaysTrue n unitBracket).numA = 0
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).numB = 1
    -- (I') alwaysFalse trajectory: bracket (2^n - 1, 2^n, n)
    ∧ (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n
    -- (II) Polynomial resolution depth: square has slope 2.
    ∧ squareIsSmooth.linearityModulus n = 2 * n
    -- (III) ConsistentOracle exists on unit bracket.
    ∧ (∃ co : ConsistentOracle unitBracket, co.oracle = alwaysTrue)
    --
... [truncated]
```

## `phaseMN_cross_track_parallel` (E213/Math/Real213/PhaseLCapstone.lean)

```lean
theorem phaseMN_cross_track_parallel (m k : Nat) :
    -- (M1) Infinitesimal gap structure: 0+ ≠ 0 at boundary.
    InfinitesimalGap (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit
                     (constCut 0 1)
    -- (M2) Riemann finite-N (POINTWISE): no π in dyadic accumulation.
    ∧ (∀ a b db n, ∃ M : Nat, ∀ m' k',
        riemannSampleSum (constCutFn (constCut a b)) db n m' k'
        = constCut M b m' k')
    -- (N3) Asymmetry: 1- = 1-exact at every (m, k).
    ∧ (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit m k
      = constCut 1 1 m k :=
  ⟨zero_plus_gap_below_ze
... [truncated]
```

## `allPhase_super_capstone` (E213/Math/Real213/PhaseLCapstone.lean)

```lean
theorem allPhase_super_capstone (n a b m k : Nat) :
    -- Phase J: dyadic IVT bracket containment
    cutLe unitBracket.leftCut
          (DyadicBracket.bisectN alwaysTrue n unitBracket).leftCut
    -- Phase K: ConsistentOracle.collapsed witness
    ∧ (∀ db, db.numA = db.numB →
        ∃ co : ConsistentOracle db, co.oracle = alwaysTrue)
    -- Phase L: trajectory closed forms
    ∧ (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n
    -- Phase L: ResolutionDepth (cube has slope 3)
    ∧ cubeIsSmooth.linearityModulus n = 3 * n
    -- Phase L: Riemann normalized average (POINTWISE).

... [truncated]
```

## `all_smooth_instances_bundle` (E213/Math/Real213/PhaseLCapstone.lean)

```lean
theorem all_smooth_instances_bundle (c : Nat → Nat → Bool) (a b : Nat) :
    -- Atomic instances
    (∃ s : IsSmooth id, s.linearityModulus 5 = 5)
    ∧ (∃ s : IsSmooth (constCutFn c), s.linearityModulus 5 = 0)
    ∧ (∃ s : IsSmooth (cutScale a b), s.linearityModulus 5 = 5)
    ∧ (∃ s : IsSmooth cutHalf, s.linearityModulus 5 = 5)
    -- Polynomial chain (degrees 2-8)
    ∧ (∃ s : IsSmooth (fun x => cutMul x x), s.linearityModulus 5 = 10)
    ∧ (∃ s : IsSmooth (fun x => cutMul x (cutMul x x)), s.linearityModulus 5 = 15)
    ∧ (∃ s : IsSmooth (fun x => cutMul (cutMul x x) (cutMul x x)),
        
... [truncated]
```

## `self_pairing_exists` (E213/Meta/AxiomMinimality.lean)

```lean
theorem self_pairing_exists :
    ∃ r : TreeFree, r = TreeFree.slash TreeFree.a TreeFree.a := by
  exact ⟨TreeFree.slash TreeFree.a TreeFree.a, rfl⟩

/-- Infinite chain of self-pairings with the same base. -/
```

## `raw_minimality_capstone` (E213/Meta/AxiomMinimalityCapstone.lean)

```lean
theorem raw_minimality_capstone :
    -- Case 1: remove `b` → all elements equal `a`
    (∀ r : RawA, r = RawA.a)
    -- Case 2: remove `a` → all elements equal `b`
    ∧ (∀ r : E213.Meta.AxiomMinimality.NoA.RawB,
         r = E213.Meta.AxiomMinimality.NoA.RawB.b)
    -- Case 3: remove `slash` → only 2 elements (a or b)
    ∧ (∀ r : E213.Meta.AxiomMinimality.NoSlash.RawAB,
         r = E213.Meta.AxiomMinimality.NoSlash.TreeAB.a
         ∨ r = E213.Meta.AxiomMinimality.NoSlash.TreeAB.b)
    -- Case 4: remove `distinctness` → self-pairing collapses
    ∧ (∃ r : E213.Meta.AxiomMinimality.NoDistin
... [truncated]
```

## `every_distinguishing_is_lens_codomain` (E213/Meta/Universal/LensClaim.lean)

```lean
theorem every_distinguishing_is_lens_codomain
    (α : Type) [d : HasDistinguishing α] :
    ∃ (L : Lens α), ∀ r : Raw, L.view r = @universalMorphism α d r := by
  refine ⟨@E213.Meta.Universal.Reflection.universalAsLens α d, ?_⟩
  intro r
  exact E213.Meta.Universal.Reflection.universalAsLens_view α r
```

## `universal_exists` (E213/Meta/UniversalLens/Core.lean)

```lean
theorem universal_exists : ∃ (α : Type) (L : Lens α), IsUniversal L :=
  ⟨Raw, idLens, idLens_is_universal⟩

/-- A universal lens refines every other lens (finest-lens property). -/
```

## `universal_lens_capstone` (E213/Meta/UniversalLens/Core.lean)

```lean
theorem universal_lens_capstone :
    (∃ (α : Type) (L : Lens α), IsUniversal L)
    ∧ (∀ {α β : Type} (L : Lens α) (M : Lens β),
         IsUniversal L → L.refines M) :=
  ⟨universal_exists, fun L M h => refines_all L M h⟩
```
