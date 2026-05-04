# Cluster `equality_match` — 38 decls (sample limited to 30)

(Auto-extracted by `tools/theorem_inspect.py`.)

## `atomic_implies_five` (E213/Firmware/Atomicity/Five.lean)

```lean
theorem atomic_implies_five (n : Nat) (h : Atomic n) : n = 5 := by
  obtain ⟨a, b, hdec, ⟨ha_odd, hb_odd⟩, huniq⟩ := h
  have ha_lt : a < 3 := by
    match Nat.lt_or_ge a 3 with
    | Or.inl h => exact h
    | Or.inr ha_ge =>
      exfalso
      have hdec' : Decomp n (a - 3) (b + 2) :=
        hdec.trans (FiveHelpers.bezout_left ha_ge)
      exact FiveHelpers.add_two_ne_self b (huniq (a - 3) (b + 2) hdec').2
  have hb_lt : b < 2 := by
    match Nat.lt_or_ge b 2 with
    | Or.inl h => exact h
    | Or.inr hb_ge =>
      exfalso
      have hdec' : Decomp n (a + 3) (b - 2) :=
        hdec.trans (
... [truncated]
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

## `decomp_5_1_eq` (E213/Math/Cohomology/Cochain/V5Decomp.lean)

```lean
theorem decomp_5_1_eq (α : Cochain 5 1) : decomp_5_1 α = α := by
  funext j
  match j with
  | ⟨0, _⟩ =>
    show (decomp_5_1 α) ⟨0, _⟩ = α ⟨0, _⟩
    unfold decomp_5_1 bz5_1 basis Cochain.add Cochain.zero
    cases (α ⟨0, by decide⟩) <;> cases (α ⟨1, by decide⟩) <;>
      cases (α ⟨2, by decide⟩) <;> cases (α ⟨3, by decide⟩) <;>
      cases (α ⟨4, by decide⟩) <;> rfl
  | ⟨1, _⟩ =>
    show (decomp_5_1 α) ⟨1, _⟩ = α ⟨1, _⟩
    unfold decomp_5_1 bz5_1 basis Cochain.add Cochain.zero
    cases (α ⟨0, by decide⟩) <;> cases (α ⟨1, by decide⟩) <;>
      cases (α ⟨2, by decide⟩) <;> cases (α ⟨3, by d
... [truncated]
```

## `cupAW_v0_v0_off_diagonal` (E213/Math/Cohomology/CupAW/Core.lean)

```lean
theorem cupAW_v0_v0_off_diagonal :
    cupAW 5 1 1 v0_5 v0_5 ⟨1, by decide⟩ = false := by decide

/-- ★ AW cup product smoke capstone — well-defined and matches
    overlap convention at the diagonal. -/
```

## `signature_d_count` (E213/Math/Cohomology/Dyadic/AtomicityConnection.lean)

```lean
theorem signature_d_count : E213.Physics.Simplex.Counts.d = 5 := rfl

/-- ★★ Signature S-side index range matches NS. -/
```

## `nextVertex_bit_inj` (E213/Math/Cohomology/Dyadic/Classifier.lean)

```lean
theorem nextVertex_bit_inj (v : Fin 5) (b₁ b₂ : Bool) :
    nextVertex v b₁ = nextVertex v b₂ → b₁ = b₂ := by
  intro h
  match v, b₁, b₂ with
  | ⟨0, _⟩, false, false => rfl
  | ⟨0, _⟩, true,  true  => rfl
  | ⟨0, _⟩, false, true  => exact absurd (Fin.mk.inj h) (by decide)
  | ⟨0, _⟩, true,  false => exact absurd (Fin.mk.inj h) (by decide)
  | ⟨1, _⟩, false, false => rfl
  | ⟨1, _⟩, true,  true  => rfl
  | ⟨1, _⟩, false, true  => exact absurd (Fin.mk.inj h) (by decide)
  | ⟨1, _⟩, true,  false => exact absurd (Fin.mk.inj h) (by decide)
  | ⟨2, _⟩, false, false => rfl
  | ⟨2, _⟩, true,  true  
... [truncated]
```

## `collTest_imp_val_eq` (E213/Math/Cohomology/Dyadic/ForwardPeriodicity.lean)

```lean
theorem collTest_imp_val_eq {N k : Nat} (g : Fin k → Fin N)
    (i j : Nat) (hi : i < k) (hj : j < k)
    (h : collisionTest g i j = true) :
    (g ⟨i, hi⟩).val = (g ⟨j, hj⟩).val := by
  show (g ⟨i, hi⟩).val = (g ⟨j, hj⟩).val
  have hu : (if h_i : i < k then
              if h_j : j < k then (g ⟨i, h_i⟩).val == (g ⟨j, h_j⟩).val
              else false
            else false) = true := h
  rw [dif_pos hi, dif_pos hj] at hu
  exact of_decide_eq_true hu

/-- Subtraction-cancellation for the pigeon collision: if both sides are
    `s · p + r` with `r < p`, equality forces both `s` and `r` to matc
... [truncated]
```

## `legendre_8_mod_7` (E213/Math/Cohomology/Dyadic/Pell/ProperBridge.lean)

```lean
theorem legendre_8_mod_7 :
    legendre213 8 7 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★ pisano_predict_proper matches TIGHT Pell proper periods. -/
```

## `fractal_edge_atomic` (E213/Math/Cohomology/Fractal/AlphaGUT.lean)

```lean
theorem fractal_edge_atomic :
    E213.Math.Cohomology.Fractal.V25.numE = 2 * 3 * 2 * 5 * 5 := by decide

/-- ★ Bridge: α_GUT structural identification.
      6  = b_1(K_5)           = numerator
      25 = numV(K_{25})        = denominator integer
      π² = ζ(2) · 6            = standard transcendental
    Therefore 1/α_GUT = 25 · ζ(2) = numV(K_{25}) · ζ(2),
    which matches `Physics.AlphaGUT` (Basel-sum bracket). -/
```

## `euler_char_K5_squared` (E213/Math/Cohomology/HodgeConjecture/Bridge/DiscreteGeometry.lean)

```lean
theorem euler_char_K5_squared : numV_K5_2 + numF_K5_2 - numE_K5_2 = 5 := by decide
/-- Equivalent rearrangement, matching the V−E+F convention. -/
```

## `b1_classes_count` (E213/Math/Cohomology/HodgeConjecture/Foundation/ConjectureLens.lean)

```lean
theorem b1_classes_count : 256 = 2 ^ 8 := by decide

/-- Cross-link: b₁ = NS² − 1 = 8 (matches `V32Betti.b1_eq_NS_sq_minus_1`
    and `PhotonKernel.b_1_eq_8`). -/
```

## `dsq_zero_prop_5_0` (E213/Math/Cohomology/Universal/Prop.lean)

```lean
theorem dsq_zero_prop_5_0 (σ : Cochain 5 0)
    (i : Fin (binom 5 2)) : delta (delta σ) i = false := by
  match hσ : σ ⟨0, by decide⟩ with
  | true =>
    have h_pt := cochain_50_true_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (fun _ : Fin (binom 5 0) => true)) i :=
      delta_pointwise_eq (delta σ) (delta _)
        (fun j => delta_pointwise_eq σ _ h_pt j) i
    rw [h_outer]
    exact aux_true_5_0 i
  | false =>
    have h_pt := cochain_50_false_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (Cochain.zero 5 0)) i :=
      delta_pointwise_eq (delt
... [truncated]
```

## `dsq_zero_prop_3_0` (E213/Math/Cohomology/Universal/Prop.lean)

```lean
theorem dsq_zero_prop_3_0 (σ : Cochain 3 0)
    (i : Fin (binom 3 2)) : delta (delta σ) i = false := by
  match hσ : σ ⟨0, by decide⟩ with
  | true =>
    have h_pt := cochain_30_true_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (fun _ : Fin (binom 3 0) => true)) i :=
      delta_pointwise_eq (delta σ) (delta _)
        (fun j => delta_pointwise_eq σ _ h_pt j) i
    rw [h_outer]
    exact aux_true_3_0 i
  | false =>
    have h_pt := cochain_30_false_at σ hσ
    have h_outer : delta (delta σ) i =
        delta (delta (Cochain.zero 3 0)) i :=
      delta_pointwise_eq (delt
... [truncated]
```

## `pattern_eq` (E213/Math/Cohomology/Universal/Prop41.lean)

```lean
theorem pattern_eq (σ : Cochain 4 1) :
    σ = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩) := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

/-- δ²=0 on every (4, 1) pattern: 16 patterns × 4 indices. -/
```

## `pattern_eq` (E213/Math/Cohomology/Universal/Prop42.lean)

```lean
theorem pattern_eq (σ : Cochain 4 2) :
    σ = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩) := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

/-- δ²=0 on every (4, 2) pattern: 64 patterns × 1 index. -/
```

## `foldr_xor_pair` (E213/Math/Cohomology/XorPairCombine.lean)

```lean
theorem foldr_xor_pair (xs : List (Bool × Bool)) (a b : Bool) :
    xs.foldr (fun p acc => xor (xor p.1 p.2) acc) (xor a b)
      = xor (xs.foldr (fun p acc => xor p.1 acc) a)
            (xs.foldr (fun p acc => xor p.2 acc) b) := by
  induction xs generalizing a b with
  | nil => rfl
  | cons hd tl ih =>
    show xor (xor hd.1 hd.2) (tl.foldr _ (xor a b))
       = xor (xor hd.1 (tl.foldr _ a)) (xor hd.2 (tl.foldr _ b))
    rw [ih a b]
    cases hd.1 <;> cases hd.2 <;>
      cases (tl.foldr (fun p acc => xor p.1 acc) a) <;>
      cases (tl.foldr (fun p acc => xor p.2 acc) b) <;> rfl

/-- Speci
... [truncated]
```

## `mul_self_mod_two` (E213/Math/Irrational/Sqrt2KernelFree.lean)

```lean
theorem mul_self_mod_two (m : Nat) : m * m % 2 = m % 2 := by
  rw [Nat.mul_mod m m 2]
  have hlt : m % 2 < 2 := Nat.mod_lt m (by decide)
  match h : m % 2, hlt with
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, hlt =>
      exfalso
      have h1 : n + 2 ≤ 1 := Nat.le_of_succ_le_succ hlt
      have h2 : n + 1 ≤ 0 := Nat.le_of_succ_le_succ h1
      exact Nat.not_succ_le_zero n h2
```

## `descent_step` (E213/Math/Irrational/Sqrt2Pure.lean)

```lean
theorem descent_step (m k : Nat) (heq : m * m = 2 * (k * k))
    (m' : Nat) (hm : m = 2 * m') :
    2 * (m' * m') = k * k := by
  rw [hm] at heq
  rw [even_sq] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq

/-- k ≠ 0 → k ≥ 1. -/
private theorem ne_zero_imp_ge_one (k : Nat) (h : k ≠ 0) : k ≥ 1 := by
  match k with
  | 0 => exact absurd rfl h
  | n + 1 => exact Nat.succ_le_succ (Nat.zero_le n)

/-- Bounded descent. -/
```

## `descent_step` (E213/Math/Irrational/Sqrt3Pure.lean)

```lean
theorem descent_step (m k : Nat) (heq : m * m = 3 * (k * k))
    (m' : Nat) (hm : m = 3 * m') :
    3 * (m' * m') = k * k := by
  rw [hm] at heq
  rw [three_mul_sq] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) heq

private theorem ne_zero_imp_ge_one (k : Nat) (h : k ≠ 0) : k ≥ 1 := by
  match k with
  | 0 => exact absurd rfl h
  | n + 1 => exact Nat.succ_le_succ (Nat.zero_le n)
```

## `descent_step` (E213/Math/Irrational/Sqrt5Pure.lean)

```lean
theorem descent_step (m k : Nat) (heq : m * m = 5 * (k * k))
    (m' : Nat) (hm : m = 5 * m') :
    5 * (m' * m') = k * k := by
  rw [hm, five_mul_sq] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) heq

private theorem ne_zero_imp_ge_one (k : Nat) (h : k ≠ 0) : k ≥ 1 := by
  match k with
  | 0 => exact absurd rfl h
  | n + 1 => exact Nat.succ_le_succ (Nat.zero_le n)
```

## `combine_proj_eq` (E213/Math/Linalg213/Chiral.lean)

```lean
theorem combine_proj_eq (v : Vec 5) (k : Fin 5) :
    combine (projS v) (projT v) k = v k := by
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl

/-- ★ Phase L4 capstone. -/
```

## `max_eq_left` (E213/Math/Max213.lean)

```lean
theorem max_eq_left {a b : Nat} (h : b ≤ a) : Nat.max a b = a :=
  match Nat.le_total a b with
  | Or.inl hab =>
    -- a ≤ b ∧ b ≤ a → a = b → max = b = a
    let h1 : Nat.max a b = b := Nat.max_eq_right hab
    let h2 : a = b := Nat.le_antisymm hab h
    h1.trans h2.symm
  | Or.inr hba =>
    -- b ≤ a from le_total — chain via Nat.max_self when a = b
    -- General case: use bridge via 213-native max_comm.
    let h1 : Nat.max a b = Nat.max b a := E213.Math.AddMod213.max_comm a b
    h1.trans (Nat.max_eq_right hba)

/-- ∅-axiom replacement for `Nat.le_max_left`. -/
```

## `partialSum_const_three_half` (E213/Math/Real213/CutSeriesConst.lean)

```lean
theorem partialSum_const_three_half (a : Nat) :
    partialSum (fun _ => constCut a 2) 3 = constCut (3*a) 2 := by
  show cutSum (partialSum (fun _ => constCut a 2) 2) (constCut a 2)
       = constCut (3*a) 2
  rw [partialSum_const_two]
  have h := cutSum_half_general (2*a) a
  rw [show (2*a + a) = 3*a from by omega] at h
  exact h

/-- **partialSum of integer constant a/1 at any n = (n*a)/1**.
    Holds for all n ≥ 0 because constCut 0 1 matches the n=0 case. -/
```

## `cutPowFnIsDifferentiable_modulus` (E213/Math/Real213/DerivativeDepth.lean)

```lean
theorem cutPowFnIsDifferentiable_modulus (n k : Nat) :
    (cutPowFnIsDifferentiable n).linearityModulus k = n * k := by
  induction n with
  | zero => show 0 = 0 * k; rw [Nat.zero_mul]
  | succ m ih =>
    show (cutPowFnIsDifferentiable m).linearityModulus k + k = (m + 1) * k
    rw [ih, E213.Tactic.Nat213.add_mul, Nat.one_mul]

/-- **Polynomial derivative resolution depth**: matches the function.
    ∅-axiom: `Nat213.add_mul` + `Max213.max_eq_left`. -/
```

## `fluxAlong_id_unitBracket` (E213/Math/Real213/FluxFTC.lean)

```lean
theorem fluxAlong_id_unitBracket :
    fluxAlong id unitBracket
      = { forward := constCut 1 1, backward := constCut 0 1 } := rfl

/-- **FTC for identity at unitBracket**: id.derivative is constant 1,
    so its integral over [0, 1] is 1, matching fluxAlong id = (1, 0). -/
```

## `ftc_id_unitBracket` (E213/Math/Real213/FluxFTC.lean)

```lean
theorem ftc_id_unitBracket :
    fluxAlong id unitBracket = ofCut (constCut 1 1) := rfl

/-- **FTC for constant function**: f(b) - f(a) is balanced (= 0)
    for any constant, matching ∫ 0 dx = 0. -/
```
