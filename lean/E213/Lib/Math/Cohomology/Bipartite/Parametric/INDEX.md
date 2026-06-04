# Bipartite/Parametric — sub-tree INDEX

Parametric (NS, NT, c)-generalization of the K_{3,2}^{(c=2)}-specific
V32 / V32Betti cohomology infrastructure (b_0 / b_1 / Euler) and the
K_{3,3}^{(c)}-specific V33EnrichedParametric enriched-2-complex
infrastructure (codim ≥ c via per-layer ψ-functionals).

**Status**: 10 files, ~187 PURE.  Direction A **CLOSED** at three
levels; universal δ⁰-kernel = constants closed structurally in
`KernelConstancyUniversal.lean`:

  1. **8-family master coverage** for `min(NS, NT) ∈ {3, 4, 5, 6}`
     (`EnrichedKNSNTcMaster.master_Knn_c_counter_resolved`).
  2. **Universal framework** (`EnrichedKNSNTcUniversal.lean`):
     central inductive theorem `foldXor_pair_lex_eq` works for ALL n
     and reduces the kill to a parity check.  Universal kill
     `kills_delta1_universal_T/S` closes any K_{NS, NT} given a
     lex-fold-compatible pair enumeration with appropriate parity.
  3. **Concrete arbitrary-NS witnesses**: provided for n ∈ {3, 4,
     5, 6}.  For n ≥ 7, construction is mechanical given
     `chooseTwo_step n : chooseTwo (n+1) = chooseTwo n + n` —
     currently blocked by `Nat.add_mul_div_right` carrying propext
     in core Lean (all `Nat.div` lemmas in core bring propext).

## File map

| File | Phase | PURE | Content |
|---|---|---|---|
| `CochSpaces.lean` | 1 | 13 | Parametric `CochV NS NT` / `CochE NS NT c` types + `srcOf` / `tgtOf` / `multOf` endpoint extractors + `srcFin` / `tgtFin` packaged + `delta0` parametric coboundary + K_{3,2}^{(c=2)} numerical sanity checks |
| `Delta0AndConnectedness.lean` | 2-3 | 16 | `cochVAt` binary-decoded cochains + `isInKerDelta0Direct` test + `kerSizeDelta0Direct` enumeration count + `b_0 = 1` (ker size = 2) verified across all G121-relevant deployments via `decide` (K_{1,1}, K_{1,2}, K_{1,3}, K_{2,2}, K_{1,4}, K_{3,2}^{(c=2)}, K_{3,3}^{(c=2)}, ...) + V32Betti compatibility |
| `EulerAndCapstone.lean` | 4-6 | 7 | `eulerChar : Int` parametric formula + `b1Formula : Nat` for connected case + chartBase-≤-5 deployment-family b_1 table + `chartVisibleAxes` bridge to KChartLens + ★★★★★★ `parametric_close_capstone` |
| `BettiOneUniversal.lean` | — | 3 | **Universal first Betti number `b₁ = E − V + 1`** from ∅-axiom `BoolEnum` cardinalities (`\|C⁰\| = 2^V`, `\|ker δ⁰\| = 2`, `\|im δ⁰\| = 2^(V−1)`) + rank-nullity/first-iso arithmetic.  `betti_one_universal` (parametric) + `betti_one_K32` (`b₁ = 8 = NS² − 1 = 1/α₃`) + `im_dim_via_transversal` (proven combinatorial half: reps count `2^(V−1)` + complement involution/transversal; only fiber=pair cited from kernel result) |
| `PathCoboundary.lean` | — | 4 | **`\|im δ⁰\| = 2^(V−1)` fully ∅-axiom**: concrete connected list-valued path coboundary `pathDelta` (consecutive XORs) + `pathDelta_complement` (surjective from head-false reps) + `pathDelta_reconstruct` (injective on head-false reps) → ★★★★★★ `im_count_inj_complement` (GENERAL: any complement-invariant + head-false-injective map has `|im| = 2^(V−1)` = rank-nullity `2^V/2`) + `im_pathDelta_card` (path instance). Removes the BettiOne image-count citation (no funext/Fintype/Nat.div) |
| `KernelConstancyUniversal.lean` | — | 20 | **Universal (∀ NS NT c) structural δ⁰-kernel = constants**, ∅-axiom for all connected K (NS≥1, NT≥1, c≥1).  Product-indexed coboundary `delta0Tri` (edges `Fin NS × Fin NT × Fin c`, no integer-decode division) + `isKer_iff_const` (kernel ⟺ globally constant) + `isKer_const_false_or_true` (kernel = exactly the 2 constants) + `isKer_root_determines` (root colour = single free parameter, dim ker = 1) + `visible_plus_one` ((NS+NT)−1 additively) + ★★★★★ `universal_kernel_close` + `const_of_constOnEdges_tRoot` / `absorber_side_gauge_free` (kernel not localized to either side) + bipartite instantiation of `Combinatorics.GraphConnectivity` (`bipAdj`, `bipAdj_connected`, `isKer_const_via_framework`) |
| `EnrichedKNSNTc.lean` | — | 63 | `(NS, NT, c)`-parametric enriched-2-complex framework + abstract Q-decomposition kill + concrete instances at every parity-OK pair.  Adds `qT_param_zero_NT5` (mirror of `qS_param_zero_NS5`) + `kills_delta1_KNS5` family + K_{4,5} and K_{5,5} closures. |
| `EnrichedKNSNTcEvenEven.lean` | — | 41 | Parity-failing closures via **vertex-excluding ψ** (both S- and T-side dual families).  Six families: `psi_excl_S0_NS{4,6}` for K_{4, NT} / K_{6, NT}; `psi_excl_T0_NT{4,6}` for K_{NS, 4} / K_{NS, 6}.  Plus concrete K_{4,4}, K_{6,4}, K_{4,6}, K_{6,6} capstones |
| `EnrichedKNSNTcUniversal.lean` | — | 14 | **Universal-`n` framework**: central inductive theorem.  `isOdd : Nat → Bool` (structural recursive parity) + `foldXor_const` / `foldXor_xor_const` (helpers) + recursive `foldXor_pair_lex n f` (abstract pair-XOR encoding the lex enumeration) + ★ `foldXor_pair_lex_eq` (central theorem: `foldXor_pair_lex n f = bif isOdd n then false else foldXor n f`).  `IsLexFold n pE` (compatibility predicate) + `qT_param_zero_universal` / `qS_param_zero_universal` (parametric `Q = 0` under `IsLexFold + isOdd`) + ★ `kills_delta1_universal_T / S` (universal kill).  Concrete `isLexFold_pairEnum3` witness + `universal_kill_for_odd_n` + `universal_kill_n3_witness`.  The framework closes the foldXor identity for ALL `n` — `pairLex_n : PairEnum n` construction for arbitrary `n ≥ 7` is mechanical given `chooseTwo_step` (currently blocked on core Lean's `Nat.add_mul_div_right` carrying propext) |
| `EnrichedKNSNTcMaster.lean` | — | 5 | **Master closure capstone** combining all eight closure families.  Six-route directory (§2 table: NS or NT ∈ {3, 4, 5, 6} ⇒ family selection).  `CClosure NS NT c pS pT` structure for uniform packaging.  `master_K33`, `master_K44`, `master_K55`, `master_K66` — K_{n,n} witnesses for n = 3, 4, 5, 6.  ★ `master_Knn_c_counter_resolved` — single statement bundling all four K_{n,n} signatures, spanning both parity-OK (n odd) and parity-failing (n even) regimes |

## Coverage

All K-deployments below are PURE-verified:
  · Trees: K_{1,1}, K_{1,2}, K_{2,1}, K_{1,3}, K_{3,1}, K_{1,4}, K_{4,1}
  · 4-cycle: K_{2,2}^{(c=1)}, K_{2,2}^{(c=2)}
  · Forced critical: K_{3,2}^{(c=2)}, K_{2,3}^{(c=2)} (S/T swap)
  · Higher chartBase: K_{3,3}^{(c=2)}

V32Betti compatibility theorem: parametric `kerSizeDelta0Direct 3 2 2`
matches `V32Betti.kerSizeDelta0` exactly.

## Universal parametric closure (structural)

`KernelConstancyUniversal.lean` closes the universal kernel statement
at the **structural** level, ∅-axiom: for all (NS ≥ 1, NT ≥ 1, c ≥ 1)
the δ⁰-kernel is exactly the two constant cochains, so `dim ker δ⁰ = 1`
(b_0 = 1) and `dim im δ⁰ = (NS + NT) − 1`.  It uses the product-indexed
coboundary `delta0Tri` to sidestep the flat-index `Nat.div` decode.

The flat-enumeration form `∀ (NS NT c), kerSizeDelta0Direct NS NT c = 2`
stays `decide`-only over the representative range: counting flat indices
pulls core Lean's `Nat.div` / `Nat.mod` lemmas, all of which carry
`propext` — an axiom-purity artifact of Lean core, not a mathematical
gap.  The product-form and flat-form kernels agree on each concrete
deployment (`decide` in `Delta0AndConnectedness.K32_matches_V32Betti`
and the representative-range theorems).

## Dependency chain

```
CochSpaces
   ├── Delta0AndConnectedness (+ V32Betti import for compatibility)
   │     └── EulerAndCapstone
   └── KernelConstancyUniversal  (structural ∀-NS-NT-c kernel close)
```

All under namespace
`E213.Lib.Math.Cohomology.Bipartite.Parametric.*`.

## Cross-references

  · `theory/math/cohomology/bipartite.md` "Parametric V32Betti"
    section — chapter narrative for this sub-tree
    — 6-phase plan + partial-close summary (deep-dive)
    V32Betti entry in spin-off marathon table
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V32Betti.lean` —
    K_{3,2}^{(c=2)}-specific predecessor
  · `lean/E213/Lib/Math/Geometry/GeometrizationConjecture/KChartLensAbstract.lean` —
    abstract axes-partition structure that this parametric machinery
    grounds at the deployment level
