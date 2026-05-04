# Cluster `equality_decide` — 1263 decls (sample limited to 50)

(Auto-extracted by `tools/theorem_inspect.py`.)

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

## `leaves_equates` (E213/Hypervisor/Lens/Instances/AB.lean)

```lean
theorem leaves_equates : Lens.leaves.view rAAB = Lens.leaves.view rABB := by decide
```

## `F3` (E213/Hypervisor/Lens/Instances/F9.lean)

```lean
abbrev F3 := Fin 3
```

## `F9` (E213/Hypervisor/Lens/Instances/F9.lean)

```lean
abbrev F9 := F3 × F3
```

## `parity_equates_ab` (E213/Hypervisor/Lens/Instances/ParityXorIncomparable.lean)

```lean
theorem parity_equates_ab :
    parityLens.view Raw.a = parityLens.view Raw.b := by decide
```

## `xor_equates` (E213/Hypervisor/Lens/Instances/ParityXorIncomparable.lean)

```lean
theorem xor_equates :
    boolXorLens.view Raw.a = boolXorLens.view rAAA := by decide
```

## `leaves_equates` (E213/Hypervisor/Lens/Leaves/DepthIncomparable.lean)

```lean
theorem leaves_equates :
    Lens.leaves.view rDeep = Lens.leaves.view rBalanced := by decide

/-- Lens.depth distinguishes them (4 vs 3). -/
```

## `depth_equates` (E213/Hypervisor/Lens/Leaves/DepthIncomparable.lean)

```lean
theorem depth_equates :
    Lens.depth.view rShallowNarrow = Lens.depth.view rShallowWide := by decide
```

## `rA1_depth_odd` (E213/Hypervisor/Lens/Morphism/NoDepthParity.lean)

```lean
theorem rA1_depth_odd : Lens.depth.view rA1 % 2 = 1 := by decide
```

## `rA3_depth_odd` (E213/Hypervisor/Lens/Morphism/NoDepthParity.lean)

```lean
theorem rA3_depth_odd : Lens.depth.view rA3 % 2 = 1 := by decide
```

## `slash12_depth_odd` (E213/Hypervisor/Lens/Morphism/NoDepthParity.lean)

```lean
theorem slash12_depth_odd : Lens.depth.view slash12 % 2 = 1 := by decide
```

## `slash32_depth_even` (E213/Hypervisor/Lens/Morphism/NoDepthParity.lean)

```lean
theorem slash32_depth_even : Lens.depth.view slash32 % 2 = 0 := by decide

/-- **Depth parity is not a slash-congruence**.  For two depth-odd
    elements (rA1, rA3) and a common rB2, the parity of the slash
    results differs. -/
```

## `leafLens_equates_slashes` (E213/Hypervisor/Lens/Properties/Leaf.lean)

```lean
theorem leafLens_equates_slashes :
    leafLens.view rAB = leafLens.view rAAB := by decide
```

## `parity_equates_leaf_slash` (E213/Hypervisor/Lens/Properties/Leaf.lean)

```lean
theorem parity_equates_leaf_slash :
    parityLens.view Raw.a = parityLens.view rAAB := by decide
```

## `leaves_equal` (E213/Hypervisor/Lens/Properties/ProdBelowId.lean)

```lean
theorem leaves_equal : Lens.leaves.view rA = Lens.leaves.view rB := by decide
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

## `K_squared` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem K_squared : (I' * J) * (I' * J) = ⟨⟨-1, 0⟩, 0⟩ := by decide

/-- Equivalently: `i · j · j = -i` (one of the four-group
    identities on the quaternion generators). -/
```

## `I_J_J` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem I_J_J : I' * (J * J) = -I' := by decide

/-- `j² = -1`. -/
```

## `J_squared` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem J_squared : J * J = ⟨⟨-1, 0⟩, 0⟩ := by decide

/-- `i² = -1`. -/
```

## `I_squared` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem I_squared : I' * I' = ⟨⟨-1, 0⟩, 0⟩ := by decide
```

## `J_mul_K` (E213/Math/CayleyDickson/CDDouble.lean)

```lean
theorem J_mul_K : J * (I' * J) = I' := by decide

/-- `k · i = j`. -/
```

## `L_squared` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem L_squared : L * L = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `I'² = -1` at Cayley (inherited). -/
```

## `I'_squared` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem I'_squared : I' * I' = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `J'² = -1` at Cayley (inherited). -/
```

## `J'_squared` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem J'_squared : J' * J' = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `I' * J' * L ≠ L * (I' * J')`.  Basis triple product
    non-commuting, octonion-flavor. -/
```

## `alt_I_I_J` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem alt_I_I_J : (I' * I') * J' = I' * (I' * J') := by decide

/-- Alternativity at `(J', I')`: `(J'·J')·I' = J'·(J'·I')`. -/
```

## `alt_J_J_I` (E213/Math/CayleyDickson/Cayley.lean)

```lean
theorem alt_J_J_I : (J' * J') * I' = J' * (J' * I') := by decide

/-- Alternativity at `(L, I')`: `(L·L)·I' = L·(L·I')`. -/
```

## `F2D` (E213/Math/CayleyDickson/F2CDTower.lean)

```lean
abbrev F2D := F2 × F2

/-- CD multiplication, char-2 version. -/
```

## `zd_product_zero` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
theorem zd_product_zero :
    zd_left * zd_right = (0 : Sedenion) := by decide

/-- `zd_left` is nonzero. -/
```

## `alt_holds_at_basis` (E213/Math/CayleyDickson/Sedenion.lean)

```lean
theorem alt_holds_at_basis :
    (e3 * e3) * e6 = e3 * (e3 * e6) := by decide

/-- **Alternativity FAILS at `(zd_left, zd_left, zd_right)`**.
    RHS = 0 since `zd_left · zd_right = 0`.  LHS non-zero;
    hence the two differ.  Closed by `decide`. -/
```

## `normSq_zero` (E213/Math/CayleyDickson/SedenionHeavy.lean)

```lean
theorem normSq_zero : normSq (0 : Sedenion) = 0 := by
  show Cayley.normSq (0 : Cayley) + Cayley.normSq (0 : Cayley) = 0
  decide

/-- **Norm multiplicativity FAILS at Sedenion.**
    `zd_left · zd_right = 0` so `|zd_left · zd_right|² = 0`,
    but `|zd_left|² · |zd_right|²` is positive.  Concrete
    witness that Sedenion is NOT a composition algebra. -/
```

## `kerSize_5_0` (E213/Math/Cohomology/BettiKernel.lean)

```lean
theorem kerSize_5_0 : kerSizeDelta 5 0 = 1 := by decide

/-- ker δ₁ on Δ⁴: σ ∈ C¹ (32 cochains) — constant cochains have
    all edge differences = 0.  Δ⁴ is the complete graph on 5
    vertices, so constants = {all-zero, all-true} ⇒ |ker δ₁| = 2. -/
```

## `kerSize_5_1` (E213/Math/Cohomology/BettiKernel.lean)

```lean
theorem kerSize_5_1 : kerSizeDelta 5 1 = 2 := by decide

/-- Reduced ℤ/2 Betti numbers for Δ⁴ (contractible).

    With our augmented convention (binom 5 0 = 1 → C⁰ has dim 1
    representing the empty face / augmentation), the cohomology is
    *reduced*:
      |ker δ_0| = 1 ⇒ dim ker δ_0 = 0
      |ker δ_1| = 2 ⇒ dim ker δ_1 = 1
      dim im δ_0 = dim C⁰ − dim ker δ_0 = 1 − 0 = 1
    So b̃_0 = 0 (= dim ker δ_0) and b̃_1 = 1 − 1 = 0. ✓ -/
```

## `cochainAt_zero_5_1` (E213/Math/Cohomology/BettiKernel.lean)

```lean
theorem cochainAt_zero_5_1 :
    isZeroBool 5 1 (cochainAt 5 1 0) = true := by decide

/-- Smoke: cochainAt 5 1 31 is the all-true cochain (5 bits set). -/
```

## `cochainAt_31_5_1_v0` (E213/Math/Cohomology/BettiKernel.lean)

```lean
theorem cochainAt_31_5_1_v0 :
    cochainAt 5 1 31 ⟨0, by decide⟩ = true := by decide
```

## `cochainAt_31_5_1_v4` (E213/Math/Cohomology/BettiKernel.lean)

```lean
theorem cochainAt_31_5_1_v4 :
    cochainAt 5 1 31 ⟨4, by decide⟩ = true := by decide
```

## `four_cycles_count` (E213/Math/Cohomology/Bipartite/Filled.lean)

```lean
theorem four_cycles_count : 3 * 1 = 3 := by decide

/-- b_1 reduction by 2-cell filling: each independent filled
    4-cycle reduces b_1 by 1. -/
```

## `delta0_v0_at_edge0` (E213/Math/Cohomology/Bipartite/V32.lean)

```lean
theorem delta0_v0_at_edge0 : delta0 v0V ⟨0, by decide⟩ = true := by decide

/-- δ₀(v0V) on edge 11 (S=2, T=4): false XOR false = false. -/
```

## `delta0_v0_at_edge11` (E213/Math/Cohomology/Bipartite/V32.lean)

```lean
theorem delta0_v0_at_edge11 : delta0 v0V ⟨11, by decide⟩ = false := by decide
```

## `kerSizeDelta0_eq_2` (E213/Math/Cohomology/Bipartite/V32Betti.lean)

```lean
theorem kerSizeDelta0_eq_2 : kerSizeDelta0 = 2 := by decide

/-- |C⁰| = 2⁵ = 32. -/
```

## `cochV_count` (E213/Math/Cohomology/Bipartite/V32Betti.lean)

```lean
theorem cochV_count : 2^5 = 32 := by decide

/-- |C¹| = 2¹² = 4096. -/
```

## `cochE_count` (E213/Math/Cohomology/Bipartite/V32Betti.lean)

```lean
theorem cochE_count : 2^12 = 4096 := by decide

/-- b₀ derivation:  dim ker δ₀ = log₂ 2 = 1  ⇒  b₀ = 1.
    Cross-checked: |ker δ₀| = 2 = 2¹.  -/
```

## `b0_eq_1` (E213/Math/Cohomology/Bipartite/V32Betti.lean)

```lean
theorem b0_eq_1 : kerSizeDelta0 = 2^1 := by decide

/-- b₁ derivation: dim im δ₀ = dim C⁰ − dim ker δ₀ = 5 − 1 = 4;
    dim H¹ = dim C¹ − dim im δ₀ = 12 − 4 = 8.
    Encoded numerically as |im δ₀| = 16 ⇒ |H¹| = 4096/16 = 256
    = 2⁸ ⇒ b₁ = 8. -/
```

## `b1_eq_NS_sq_minus_1` (E213/Math/Cohomology/Bipartite/V32Betti.lean)

```lean
theorem b1_eq_NS_sq_minus_1 : 8 = 3 * 3 - 1 := by decide

/-- ★ Phase CE capstone: K_{3,2}^{(2)} cohomology computed at
    full cochain level.
      b₀ = 1    (connected graph)
      b₁ = 8    (= NS² − 1 = 1/α₃ confined coupling)
      b_k = 0   (k ≥ 2, since K_{3,2}^{(2)} is 1-dimensional)
    Re-establishes PhotonKernel.b_1_eq_8 at the chain level. -/
```

## `chi_3_glued_eq_3` (E213/Math/Cohomology/ClosureExtension.lean)

```lean
theorem chi_3_glued_eq_3 : chi_3_glued = 3 := by decide

/-- N=4 cells: 5 - 10 + 10 - 5 + 4 = 4. -/
```

## `chi_4_glued_eq_4` (E213/Math/Cohomology/ClosureExtension.lean)

```lean
theorem chi_4_glued_eq_4 : chi_4_glued = 4 := by decide

/-- N=2 (S⁴) and N=N (any) Euler relation, Int arithmetic. -/
```

## `dim_C0` (E213/Math/Cohomology/Cochain/Core.lean)

```lean
theorem dim_C0 : binom d 0 = 1  := by decide
```

## `dim_C1` (E213/Math/Cohomology/Cochain/Core.lean)

```lean
theorem dim_C1 : binom d 1 = 5  := by decide
```

## `dim_C2` (E213/Math/Cohomology/Cochain/Core.lean)

```lean
theorem dim_C2 : binom d 2 = 10 := by decide
```

## `dim_C3` (E213/Math/Cohomology/Cochain/Core.lean)

```lean
theorem dim_C3 : binom d 3 = 10 := by decide
```

## `dim_C4` (E213/Math/Cohomology/Cochain/Core.lean)

```lean
theorem dim_C4 : binom d 4 = 5  := by decide
```
