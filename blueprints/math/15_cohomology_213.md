# Cohomology 213 — Blueprint

**Priority**: ★★★ Top priority (motivated by α_em 5.4×10⁻⁴ structural
gap; bridges Real213 cohomological calculus + Physics simplicial chain)

---

## 1. Why This Field

ZFC algebraic topology:
- Singular / simplicial chain complex over ℤ
- Homology / cohomology defined via free abelian groups + boundary
- Depends on Choice for simplicial set theory; Mathlib uses a heavy
  category-theoretic framework

Natural emergence in 213:
- **Cohomological calculus already in place** (Real213FluxCut /
  FluxCochain / FluxDivergence — F1 finding: ∂ = ∇ = MVT = FTC unified)
- **Simplicial face counts already in place** (Physics/SimplexCounts:
  Hodge duality C(5,k)=C(5,d-k) verified; FaceTerms: 4-cycles, tet
  per vertex)
- **First Betti number already computed** (PhotonKernel: b₁ = NS²−1)
- **Five-term simplicial decomposition of α_em already proven**
  (AlphaEMSimplicial: each prefactor is K_{NS,NT}^{(c)} ⊂ Δ⁴ invariant)

Missing: a *systematic* cochain complex with δ²=0, cup product,
higher Betti numbers, Hodge decomposition — all expressible in
finite-rational-decidable form. The 5.4×10⁻⁴ gap to observed 1/α_em
is the immediate physics motivation: candidate sixth simplicial
invariant most likely lives in cup product or H².

## 2. 213-native Emergence — 5 Paths

### 2.1 Cochain complex on Δᵈ
`Cᵏ(Δᵈ) := Lens (Fin (binom d k) → Lens α)`. Coboundary δ from
inclusion-exclusion on faces. Decidable for finite d.

### 2.2 K_{NS,NT}^{(c)} graph cohomology
b₀, b₁ already known (PhotonKernel). Extend to b₂ via 2-cycles
(squares, hexagons in the multigraph). Computed by Euler-style
formula extension.

### 2.3 Cup product Cᵏ × Cˡ → Cᵏ⁺ˡ
Bilinear; satisfies Leibniz w.r.t. δ. Generates ring structure on
H*. Cross-terms in cohomology product are the prime candidate for
the α_em gap.

### 2.4 Hodge decomposition for K_{NS,NT}^{(c)}
Already see `hodge_*` lemmas in SimplexCounts at the dim level —
extend to the full chain-level Hodge map ⋆: Cᵏ → Cᵈ⁻ᵏ.

### 2.5 Bridge to Real213 (cohomological calculus)
`FluxCut` is a 1-cochain on a dyadic interval. Generalize to
k-cochains on dyadic k-cells; recover MVT and FTC as δ-closure
identities at all dimensions.

## 3. Already-Laid Building Blocks

| Tool | Module | Purpose |
|---|---|---|
| `FluxCut`, `cohomEquiv` | `Real213FluxCut/Equiv` | 1-cochain |
| `fluxAlong`, `localDivergence` | `Real213FluxCochain/Divergence` | δ on 0/1 cells |
| `binom`, `lambda_dim` | `Physics/SimplexCounts` | face counts on Δᵈ |
| `hodge_1..hodge_4` | `Physics/SimplexCounts` | Hodge dim duality |
| `b_1`, `num_edges`, `num_vertices` | `Physics/PhotonKernel` | b₀, b₁ on graph |
| `four_cycles_count`, `tetrahedra_per_vertex` | `Physics/FaceTerms` | 4-cycles, tet links |
| `alpha_em_simplicial_capstone` | `Physics/AlphaEMSimplicial` | five-term sum |
