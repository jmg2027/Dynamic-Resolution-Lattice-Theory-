# Cohomology — Module Index

213-native algebraic topology + simplicial cohomology.  ~305 files
across 14 sub-clusters + 17 top-level.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `HodgeConjecture/` | 75 | HC²¹³ programme (Foundation / Refinement / Bridges) |
| `Bipartite/` | 59 | K_{3,2}^{(c=2)}, K_{3,3}^{(c=2,3)} multigraph cohomology, Massey products, ψ-kernel, parametric |
| `CupAW/` | 30 | Alexander–Whitney cup (homotopy-coherent variant) |
| `Cup/` | 30 | strict cup product on Cochains |
| `Fractal/` | 30 | fractal-lens parametric configuration count (`configCountD`) |
| `Universal/` | 10 | δ²=0 Prop-level universal lift |
| `Hodge/` | 11 | Δ-Laplacian + ⋆-involution machinery |
| `Examples/` | 9 | BettiKernel, K5, Diamond, EulerClosed, EncodingBijection, SimplexBasis |
| `Bridge/` | 10 | AlphaEMBridge, Real213Bridge, Paper1Chiral, ClosureExtension, PredicateAsCochain, etc. |
| `Surfaces/` | 9 | concrete surface examples (T² Minimal + T² Squared) |
| `Delta/` | 5 | δ : Cᵏ → Cᵏ⁺¹ coboundary |
| `Cochain/` | 5 | 213-native cochain complex foundation |
| `Tripartite/` | 4 | K_{2,1,3} tripartite cohomology + V32/V213 bridge |
| `Infrastructure/` | 1 | shared infrastructure |

## Top-level (17 files)

Umbrellas: Cochain, Cup, CupAW, Delta, Fractal, Hodge,
HodgeConjecture, Bipartite, Surfaces, Universal, Tripartite.

Content files: `Capstone.lean` (final bundle),
`BipartiteStermBrocotClassification.lean`,
`CrossGraphPattern.lean` (cross-graph pattern transfer),
`K33Unified.lean` (K_{3,3} unified closure),
`MediantCohomologyFunctor.lean` (mediant → cohomology functor),
`NodupAsClause4.lean`.

`Cohomology.lean` — single import for downstream.
