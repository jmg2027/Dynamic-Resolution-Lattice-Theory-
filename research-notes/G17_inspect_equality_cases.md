# Cluster `equality_cases` — 105 decls (sample limited to 30)

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

## `transportTree_roundtrip` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem transportTree_roundtrip
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (t : Tree) (hcanon : canonicalBy cmp2 t = true) :
    transportTree cmp2 (transportTree cmp1 t) = t := by
  induction t with
  | a => rfl
  | b => rfl
  | slash s u ihs ihu =>
      have hsu : cmp2 s u = .lt := canonicalBy_slash_lt hcanon
      unfold canonicalBy at hcanon
      rw [Bool.and_eq_true, Bool.and_eq_true] at hcanon
      obtain ⟨⟨hcs, hcu⟩, _⟩ := hcanon
      have ihs' := ihs hcs
      have ihu' := ihu hcu
      rw [transportTree_slash]
      cases hcmp1 : cmp
... [truncated]
```

## `transportTree_canonical` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
theorem transportTree_canonical
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (t : Tree) (hcanon1 : canonicalBy cmp1 t = true) :
    canonicalBy cmp2 (transportTree cmp2 t) = true := by
  induction t with
  | a => rfl
  | b => rfl
  | slash s u ihs ihu =>
      have hsu1 : cmp1 s u = .lt := canonicalBy_slash_lt hcanon1
      unfold canonicalBy at hcanon1
      rw [Bool.and_eq_true, Bool.and_eq_true] at hcanon1
      obtain ⟨⟨hcs, hcu⟩, _⟩ := hcanon1
      have ihs' := ihs hcs
      have ihu' := ihu hcu
      -- transportTree cmp2 s, u canonical-by-c
... [truncated]
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

## `boolToConstLens_xor` (E213/Hypervisor/Lens/Compose/OnLensImage.lean)

```lean
theorem boolToConstLens_xor (x y : Bool) :
    boolToConstLens (xor x y) =
      lensXor (boolToConstLens x) (boolToConstLens y) := by
  cases x <;> cases y <;>
    simp [boolToConstLens, lensXor_TT, lensXor_TF, lensXor_FT, lensXor_FF]
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

## `negSqLens_sq` (E213/Hypervisor/Lens/Instances/NegSq.lean)

```lean
theorem negSqLens_sq (v : Bool) : sq negSqLens v = !v := by
  cases v <;> rfl

/-- negSqLens is not Idempotent (sq v = !v ≠ v). -/
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

## `sumCombine_comm` (E213/Hypervisor/Lens/Instances/Sum.lean)

```lean
theorem sumCombine_comm {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (x y : Sum α β) :
    sumCombine x y = sumCombine y x := by
  cases x <;> cases y <;> simp [sumCombine, d_α.combine_sym, d_β.combine_sym]
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

## `parityLens_collapse_false` (E213/Hypervisor/Lens/Properties/ParityCollapseFalse.lean)

```lean
theorem parityLens_collapse_false (x : Bool) :
    parityLens.combine x x = false := by
  cases x <;> rfl
```

## `sub_one_add_one` (E213/Kernel/Tactic/Nat213.lean)

```lean
theorem sub_one_add_one {n : Nat} (h : n ≠ 0) : n - 1 + 1 = n := by
  cases n with
  | zero => exact absurd rfl h
  | succ k => rfl

/-- General `Nat.sub_add_cancel`: `m ≤ n → n - m + m = n`.  ∅-axiom
    via direct recursion on `m`. -/
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

## `zero_mod` (E213/Math/AddMod213.lean)

```lean
theorem zero_mod (a : Nat) : 0 % a = 0 := by
  by_cases h : 0 < a
  · exact Nat.mod_eq_of_lt h
  · have : a = 0 := Nat.eq_zero_of_not_pos h
    subst this; rfl

/-- `(a % b + c) % b = (a + c) % b` when `0 < b`.  ∅-axiom. -/
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

## `diagonal_seq_orderProj_const` (E213/Math/Cauchy/Archimedean.lean)

```lean
theorem diagonal_seq_orderProj_const (m k : Nat) (n : Nat) (hn : n ≥ 1) :
    orderProj m k (n, n) = decide (k ≤ m) := by
  unfold orderProj
  show decide (n * k ≤ n * m) = decide (k ≤ m)
  by_cases hkm : k ≤ m
  · have h : n * k ≤ n * m := Nat.mul_le_mul_left n hkm
    exact (decide_eq_true h).trans (decide_eq_true hkm).symm
  · have hnot : ¬ n * k ≤ n * m :=
      fun h' => hkm (Nat.le_of_mul_le_mul_left h' hn)
    exact (decide_eq_false hnot).trans (decide_eq_false hkm).symm
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

## `ext` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem ext {u v : Lipschitz} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- **Conjugation** on `Lipschitz`: flip imaginary, ZI-conj the real. -/
```

## `ext` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem ext {u v : Cayley} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- CD multiplication (same formula as layer 1, lifted). -/
```

## `ext` (E213/Math/CayleyDickson/Pathion.lean)

```lean
theorem ext {u v : Pathion} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr
```

## `ext` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
theorem ext {u v : Sedenion} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr
```

## `ext` (E213/Math/CayleyDickson/Trigintaduonion.lean)

```lean
theorem ext {u v : Trigintaduonion} (hr : u.re = v.re)
    (hi : u.im = v.im) : u = v := by cases u; cases v; congr

/-- CD multiplication (same formula, lifted once more). -/
```

## `ext` (E213/Math/CayleyDickson/ZI.lean)

```lean
theorem ext {u v : ZI} (hr : u.re = v.re) (hi : u.im = v.im) : u = v := by
  cases u; cases v; congr
```
