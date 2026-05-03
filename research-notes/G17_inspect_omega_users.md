# Cluster `omega_users` — 111 decls (sample limited to 40)

(Auto-extracted by `tools/theorem_inspect.py`.)

## `count_eq_one_iff` (E213/Firmware/Atomicity/PairForcing.lean)

```lean
theorem count_eq_one_iff
    (p q : Nat) (hp : 2 ≤ p) (hpq : p < q) (hcop : Nat.gcd p q = 1) :
    count p q = 1 ↔ (p = 2 ∧ q = 3) := by
  unfold count
  have hq : 2 ≤ q := by omega
  have hp_pos : 1 ≤ p / 2 := by omega
  have hq_pos : 1 ≤ q / 2 := by omega
  constructor
  · intro h
    obtain ⟨hp2, hq2⟩ := mul_eq_one_of_pos _ _ hp_pos hq_pos h
    have hp_cases : p = 2 ∨ p = 3 := (div_two_eq_one_iff p hp).mp hp2
    have hq_cases : q = 2 ∨ q = 3 := (div_two_eq_one_iff q hq).mp hq2
    -- p < q + p, q ∈ {2, 3} → (p, q) = (2, 3)
    rcases hp_cases with rfl | rfl <;> rcases hq_cases with rfl | 
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

## `leavesMod3Lens` (E213/Hypervisor/Lens/Leaves/Mod3.lean)

```lean
def leavesMod3Lens : Lens (Fin 3) where
  base_a := ⟨1, by decide⟩
  base_b := ⟨1, by decide⟩
  combine := f3add

private theorem f3add_comm (a b : Fin 3) : f3add a b = f3add b a := by
  unfold f3add; congr 1; omega

private theorem f3add_mod (a b : Nat) :
    (a % 3 + b % 3) % 3 = (a + b) % 3 := by
  rw [← Nat.add_mod]
```

## `refines_implies_divides` (E213/Hypervisor/Lens/Leaves/ModNat.lean)

```lean
theorem refines_implies_divides (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hrefines : (leavesModNat m).refines (leavesModNat k)) :
    k ∣ m := by
  obtain ⟨r, hr⟩ := E213.Infinity.leaves_surjective_pos (m + 1) (by omega)
  have h_leaves_a : Lens.leaves.view Raw.a = 1 := rfl
  -- In mod m, Raw.a and r are equal (both have leaves ≡ 1 mod m)
  have hm_eq : (leavesModNat m).view Raw.a = (leavesModNat m).view r := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, h_leaves_a, hr]
    show 1 % m = (m + 1) % m
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  -- By refines, they are also 
... [truncated]
```

## `leafLens` (E213/Hypervisor/Lens/Properties/Leaf.lean)

```lean
def leafLens : Lens Bool where
  base_a := false
  base_b := false
  combine _ _ := true

/-- leaves r ≥ 1 for all r : Raw. -/
private theorem leaves_ge_one : ∀ r : Raw, 1 ≤ Lens.leaves.view r := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]; omega

/-- leafLens.view r = decide (leaves r ≥ 2). -/
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

## `ex` (E213/Kernel/Tactic/Omega213.lean)

```lean
theorem ex (n : Nat) (h : 1 ≤ n) : 2 * n ≥ 2 := by omega213
#print axioms ex   -- "does not depend on any axioms"
```

## What it covers

The current implementation handles 213's four most common patterns:

  1. **Concrete decidable goals** — `decide` first.
  2. **Bounded inequalities** — `Nat.le_succ_of_le`,
     `Nat.lt_succ_of_le`, `Nat.lt_of_le_of_lt`, etc.
  3. **Multiplicative monotonicity** — `Nat.mul_le_mul_left`,
     `Nat.mul_le_mul_right`.
  4. **Positivity / non-zero** — `Nat.pos_of_ne_zero`,
     `Nat.zero_lt_succ`.

Goals that don't fall to these patterns will fail; convert manu
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

## `profinite_factorial_is_GFCauchy` (E213/Math/Cauchy/GenericFamily.lean)

```lean
theorem profinite_factorial_is_GFCauchy
    (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n)
                 = E213.Math.Cauchy.ProfiniteSeq.factorial (n + 1)) :
    GFCauchy Lens.leaves (fun (m : Nat) (n : Nat) => n % (m + 1)) xs := by
  intro m
  refine ⟨m + 1, ?_⟩
  intro k l hk hl
  show Lens.leaves.view (xs k) % (m + 1) = Lens.leaves.view (xs l) % (m + 1)
  rw [hLeaves k, hLeaves l]
  rw [E213.Math.Cauchy.ProfiniteSeq.factorial_eventually_zero_mod (m+1) (by omega) k (by omega),
      E213.Math.Cauchy.ProfiniteSeq.factorial_eventually_zero_mod (m+1) (by omega) l (by omega)]
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

## `factorial_dvd` (E213/Math/Cauchy/ProfiniteSeq.lean)

```lean
theorem factorial_dvd (m n : Nat) (h : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ factorial n := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hkm : m ≤ k
      · have hdvd : m ∣ factorial k := ih hkm
        show m ∣ (k+1) * factorial k
        obtain ⟨q, hq⟩ := hdvd
        refine ⟨(k+1) * q, ?_⟩
        calc (k + 1) * factorial k = (k + 1) * (m * q) := by rw [hq]
          _ = m * ((k + 1) * q) := by
              rw [← Nat.mul_assoc]
              rw [Nat.mul_comm (k + 1) m]
              rw [Nat.mul_assoc]
      · have hmk1 : m = k + 1 := by omega
        show m ∣ (k+1) * fa
... [truncated]
```

## `factorial_seq_cauchy` (E213/Math/Cauchy/ProfiniteSeq.lean)

```lean
theorem factorial_seq_cauchy (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    LensCauchy (leavesModNat m) xs := by
  refine ⟨m, ?_⟩
  intro k l hk hl
  show (leavesModNat m).view (xs k) = (leavesModNat m).view (xs l)
  rw [leavesModNat_view_eq, leavesModNat_view_eq]
  rw [hLeaves k, hLeaves l]
  rw [factorial_eventually_zero_mod m (by omega) k (by omega)]
  rw [factorial_eventually_zero_mod m (by omega) l (by omega)]

/-- **Profinite limit**: the leavesModNat m limit of the
    factorial-leaves sequence is 0.  Corresponds exactl
... [truncated]
```

## `factorial_seq_limit_zero` (E213/Math/Cauchy/ProfiniteSeq.lean)

```lean
theorem factorial_seq_limit_zero (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    EventuallyClass (leavesModNat m) xs 0 := by
  refine ⟨m, ?_⟩
  intro n hn
  show (leavesModNat m).view (xs n) = 0
  rw [leavesModNat_view_eq, hLeaves n]
  exact factorial_eventually_zero_mod m (by omega) n (by omega)

/-- **Family Cauchy** w.r.t. leavesModNat family ({m : m ≥ 2}). -/
```

## `wallis_sharper_lower` (E213/Math/Cauchy/WallisSharper.lean)

```lean
theorem wallis_sharper_lower (n : Nat) (hn : n ≥ 2) :
    45 * wallisNum n ≥ 64 * wallisDen n := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 1
      · subst hk
        show 45 * wallisNum 2 ≥ 64 * wallisDen 2
        decide
      · have hk2 : k ≥ 2 := by omega
        have h_inv := ih hk2
        have h_poly := poly_ineq k
        show 45 * (wallisNum k * (4 * (k+1) * (k+1))) ≥
             64 * (wallisDen k * ((2*k+1) * (2*k+3)))
        -- IH * (4*(k+1)*(k+1)) and poly * (64 * wallisDen k)
        have h1 : 45 * wallisNum k * (4 * (k+1) * (k+1)) ≥
       
... [truncated]
```

## `conj_conj` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem conj_conj (u : Lipschitz) : (conj (conj u)) = u := by
  apply ext
  · show u.re.conj.conj = u.re
    exact ZI.conj_conj u.re
  · show -(-u.im) = u.im
    apply ZI.ext
    · show -(-u.im.re) = u.im.re; omega
    · show -(-u.im.im) = u.im.im; omega

/-- `conj` is not the identity. -/
```

## `conj_mul_anti` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem conj_mul_anti (u v : Lipschitz) :
    Lipschitz.conj (u * v) = Lipschitz.conj v * Lipschitz.conj u := by
  apply ext
  · show (u.re * v.re - v.im.conj * u.im).conj
         = v.re.conj * u.re.conj - (-u.im).conj * (-v.im)
    rw [ZI.conj_sub, ZI.conj_mul, ZI.conj_mul, ZI.conj_conj,
        ZI.conj_neg, ZI.neg_mul, ZI.mul_neg, ZI.neg_neg,
        ZI.mul_comm u.re.conj v.re.conj,
        ZI.mul_comm v.im u.im.conj]
  · show -(v.im * u.re + u.im * v.re.conj)
         = (-u.im) * v.re.conj + (-v.im) * (u.re.conj).conj
    rw [ZI.conj_conj, ZI.neg_mul, ZI.neg_mul]
    apply ZI.ext
    · sho
... [truncated]
```

## `conj_conj` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem conj_conj (u : Cayley) : conj (conj u) = u := by
  apply ext
  · show u.re.conj.conj = u.re
    exact Lipschitz.conj_conj u.re
  · show -(-u.im) = u.im
    apply Lipschitz.ext
    · show (-(-u.im)).re = u.im.re
      apply ZI.ext
      · show -(-u.im.re.re) = u.im.re.re; omega
      · show -(-u.im.re.im) = u.im.re.im; omega
    · show (-(-u.im)).im = u.im.im
      apply ZI.ext
      · show -(-u.im.im.re) = u.im.im.re; omega
      · show -(-u.im.im.im) = u.im.im.im; omega

/-- `Cayley.conj` is not the identity. -/
```

## `normSq_eq_zero_iff` (E213/Math/CayleyDickson/CayleyHeavy.lean)

```lean
theorem normSq_eq_zero_iff (u : Cayley) : normSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h1 := lip_normSq_nonneg u.re
    have h2 := lip_normSq_nonneg u.im
    have hre_z : Lipschitz.normSq u.re = 0 := by
      change Lipschitz.normSq u.re + Lipschitz.normSq u.im = 0 at h
      omega
    have him_z : Lipschitz.normSq u.im = 0 := by
      change Lipschitz.normSq u.re + Lipschitz.normSq u.im = 0 at h
      omega
    have hre : u.re = 0 := (Lipschitz.normSq_eq_zero_iff u.re).mp hre_z
    have him : u.im = 0 := (Lipschitz.normSq_eq_zero_iff u.im).mp him_z
    show u = ⟨0, 0⟩
    app
... [truncated]
```

## `normSq_eq_zero_iff` (E213/Math/CayleyDickson/LipschitzHeavy.lean)

```lean
theorem normSq_eq_zero_iff (u : Lipschitz) : normSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    show u = ⟨0, 0⟩
    apply ext
    · show u.re = (0 : ZI)
      apply ZI.ext
      · show u.re.re = 0
        have : u.re.re * u.re.re + u.re.im * u.re.im +
                (u.im.re * u.im.re + u.im.im * u.im.im) = 0 := h
        have h1 : 0 ≤ u.re.re * u.re.re := IntHelpers.mul_self_nonneg _
        have h2 : 0 ≤ u.re.im * u.re.im := IntHelpers.mul_self_nonneg _
        have h3 : 0 ≤ u.im.re * u.im.re := IntHelpers.mul_self_nonneg _
        have h4 : 0 ≤ u.im.im * u.im.im := IntHelpers.mul_sel
... [truncated]
```

## `sub_re` (E213/Math/CayleyDickson/ZIArith.lean)

```lean
theorem sub_re (u v : ZI) : (u - v).re = u.re - v.re := by
  show (u + (-v)).re = u.re - v.re
  rw [add_re, neg_re]; omega
```

## `sub_im` (E213/Math/CayleyDickson/ZIArith.lean)

```lean
theorem sub_im (u v : ZI) : (u - v).im = u.im - v.im := by
  show (u + (-v)).im = u.im - v.im
  rw [add_im, neg_im]; omega
```

## `add_zero` (E213/Math/CayleyDickson/ZIArith.lean)

```lean
theorem add_zero (u : ZI) : u + 0 = u := by
  apply ext
  · show u.re + 0 = u.re; omega
  · show u.im + 0 = u.im; omega
```

## `zero_add` (E213/Math/CayleyDickson/ZIArith.lean)

```lean
theorem zero_add (u : ZI) : 0 + u = u := by
  apply ext
  · show 0 + u.re = u.re; omega
  · show 0 + u.im = u.im; omega
```

## `add_comm` (E213/Math/CayleyDickson/ZIArith.lean)

```lean
theorem add_comm (u v : ZI) : u + v = v + u := by
  apply ext
  · show u.re + v.re = v.re + u.re; omega
  · show u.im + v.im = v.im + u.im; omega
```

## `normSq_nonneg` (E213/Math/CayleyDickson/ZIDomain.lean)

```lean
theorem normSq_nonneg (u : ZI) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + u.im * u.im
  have h1 := IntHelpers.mul_self_nonneg u.re
  have h2 := IntHelpers.mul_self_nonneg u.im
  omega
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

## `conj_conj` (E213/Math/CayleyDickson/ZOmega.lean)

```lean
theorem conj_conj (u : ZOmega) : u.conj.conj = u := by
  apply ext
  · show (u.re - u.im) - (-u.im) = u.re
    omega
  · show -(-u.im) = u.im
    omega
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

## `normSq_nonneg` (E213/Math/CayleyDickson/ZOmegaDomain.lean)

```lean
theorem normSq_nonneg (u : ZOmega) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re - u.re * u.im + u.im * u.im
  have h_a2 := IntHelpers.mul_self_nonneg u.re
  have h_b2 := IntHelpers.mul_self_nonneg u.im
  by_cases hab : 0 ≤ u.re * u.im
  · -- 0 ≤ ab.  Use (a - b)² = a² - 2ab + b² ≥ 0.
    have h_sub := IntHelpers.mul_self_nonneg (u.re - u.im)
    have h_exp : (u.re - u.im) * (u.re - u.im)
               = u.re*u.re - 2*(u.re*u.im) + u.im*u.im := by
      have : (u.re - u.im) * (u.re - u.im)
           = u.re*u.re - u.re*u.im - (u.im*u.re - u.im*u.im) := by
        rw [Int.sub_mul, Int.mul_sub, I
... [truncated]
```

## `normSq_eq_zero_iff` (E213/Math/CayleyDickson/ZOmegaDomain.lean)

```lean
theorem normSq_eq_zero_iff (u : ZOmega) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h_eq : u.re * u.re - u.re * u.im + u.im * u.im = 0 := h
    have h_a2 := IntHelpers.mul_self_nonneg u.re
    have h_b2 := IntHelpers.mul_self_nonneg u.im
    -- Case-split on sign of ab to derive a*a = 0 ∧ b*b = 0
    have h_ab : u.re * u.im = 0 := by
      by_cases hab : 0 ≤ u.re * u.im
      · -- (a-b)² = a²-2ab+b² ≥ 0, with normSq=0 → a²+b²=ab → 2ab=2(a²+b²)/(...)...
        -- Use: 0 = a²+b²-ab and 2ab ≤ a²+b² (from (a-b)²≥0)
        have h_sub := IntHelpers.mul_self_nonneg (u.re - u
... [truncated]
```

## `normSq_nonneg` (E213/Math/CayleyDickson/ZSqrt2Domain.lean)

```lean
theorem normSq_nonneg (u : Z2) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + 2 * (u.im * u.im)
  have h1 := IntHelpers.mul_self_nonneg u.re
  have h2 := IntHelpers.mul_self_nonneg u.im
  omega
```

## `normSq_eq_zero_iff` (E213/Math/CayleyDickson/ZSqrt2Domain.lean)

```lean
theorem normSq_eq_zero_iff (u : Z2) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    have h_eq : u.re * u.re + 2 * (u.im * u.im) = 0 := h
    have hre : u.re * u.re = 0 := by omega
    have him : u.im * u.im = 0 := by omega
    apply ext
    · exact IntHelpers.mul_self_eq_zero.mp hre
    · exact IntHelpers.mul_self_eq_zero.mp him
  · rintro rfl
    show (0 : Int) * 0 + 2 * (0 * 0) = 0
    simp
```

## `normSq_nonneg` (E213/Math/CayleyDickson/ZSqrtDomain.lean)

```lean
theorem normSq_nonneg (hD : 0 ≤ D) (u : ZSqrt D) :
    0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + D * (u.im * u.im)
  have h1 := IntHelpers.mul_self_nonneg u.re
  have h2 := IntHelpers.mul_self_nonneg u.im
  have h3 : 0 ≤ D * (u.im * u.im) := Int.mul_nonneg hD h2
  omega
```

## `normSq_eq_zero_iff` (E213/Math/CayleyDickson/ZSqrtDomain.lean)

```lean
theorem normSq_eq_zero_iff (hD : 0 < D) (u : ZSqrt D) :
    u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h_eq : u.re * u.re + D * (u.im * u.im) = 0 := h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    have hDnn : (0 : Int) ≤ D := by omega
    have h3 : 0 ≤ D * (u.im * u.im) := Int.mul_nonneg hDnn h2
    have hre : u.re * u.re = 0 := by omega
    have hd_im : D * (u.im * u.im) = 0 := by omega
    have him : u.im * u.im = 0 := by
      rcases Int.mul_eq_zero.mp hd_im with h | h
      · omega
      · exact h
    apply ext
    
... [truncated]
```

## `canonicalAndMap_iff_eq_a` (E213/Math/Choice/CanonicalTruthChar.lean)

```lean
theorem canonicalAndMap_iff_eq_a (r : Raw) :
    canonicalAndMap r ↔ r = Raw.a := by
  induction r using Raw.rec with
  | a =>
      rw [canonicalAndMap_a]
      simp
  | b =>
      rw [canonicalAndMap_b]
      constructor
      · intro h; exact absurd h (fun e => e)
      · intro heq; exact absurd heq (by decide)
  | slash x y h ihx ihy =>
      rw [canonicalAndMap_slash x y h]
      constructor
      · rintro ⟨hx_and, hy_and⟩
        have hx_eq : x = Raw.a := ihx.mp hx_and
        have hy_eq : y = Raw.a := ihy.mp hy_and
        rw [hx_eq, hy_eq] at h
        exact absurd rfl h
      · intro 
... [truncated]
```

## `BitAuto2` (E213/Math/Cohomology/Dyadic/BitAuto2.lean)

```lean
def BitAuto2.run {n : Nat} (m : BitAuto2 n) (k bound : Nat) : Fin n :=
  (List.range bound).foldl (fun s i => m.step s (bit213 k i)) m.init

/-- Bit at index k, with bound for digit count. -/
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

## `fsm_one_third_run_val` (E213/Math/Cohomology/Dyadic/BitFSM/Examples.lean)

```lean
theorem fsm_one_third_run_val (k : Nat) :
    (fsm_one_third.run k).val = k % 2 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show (fsm_one_third.step (fsm_one_third.run k')).val = (k' + 1) % 2
    have h_val_lt : (fsm_one_third.run k').val < 2 :=
      (fsm_one_third.run k').isLt
    rcases Nat.lt_or_ge (fsm_one_third.run k').val 1 with h0 | h1
    · -- val = 0
      have hval : (fsm_one_third.run k').val = 0 := by omega
      have hrun : fsm_one_third.run k' = ⟨0, by decide⟩ := Fin.ext hval
      rw [hrun]; show 1 = (k' + 1) % 2
      rw [hval] at ih; omega
    · -- val = 1

... [truncated]
```

## `pellFSMmodP_run_period_N` (E213/Math/Cohomology/Dyadic/FSMGeneralPeriod.lean)

```lean
theorem pellFSMmodP_run_period_N :
    ∀ k, pellFSMmodP.run (k + N) = pellFSMmodP.run k := by
  intro k
  induction k with
  | zero => decide  -- proves run N = init via N-step compute
  | succ k' ih =>
    show pellFSMmodP.step (pellFSMmodP.run (k' + N))
        = pellFSMmodP.step (pellFSMmodP.run k')
    rw [ih]
```

Two parts:
  1. base case: `run N = init` (decidable for specific N)
  2. step: `step (run (k+N)) = step (run k)` (immediate from IH)

This file abstracts (2) into a UNIVERSAL theorem.

## What's proved

  ArithFSM2.run_period_of_init : ∀ m N,
    m.run N = m.init → ∀ k, m.run (
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
