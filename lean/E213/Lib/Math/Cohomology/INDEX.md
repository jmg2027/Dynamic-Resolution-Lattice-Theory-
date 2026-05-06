# Math/Cohomology/ — sub-cluster index

After Phase 3 + Phase 7 reorg (2026-05-01), this directory is
organized into topical sub-clusters.

## Sub-directories (10 sub-clusters, ~175 files)

| Subdir | Files | Topic |
|---|---|---|
| `Bipartite/` | 3 | K_{3,2}^{(c=2)} bipartite graph (V32, V32Betti, Filled) |
| `Cochain/` | 4 | Cochain framework (Core, V5{Decomp, _1DecompR, _2Decomp}) |
| `Cup/` | 3 | Cup product (Core, Ring, Leibniz) |
| `CupAW/` | 20 | Cup-AW Leibniz family (CupAW.Leibniz* steps to Δ⁴ capstone) |
| `Delta/` | 5 | δ operator (Core, Linear, SqZero, V4Capstone, V4LeibnizCapstone) |
| `Fractal/` | 3 | Fractal levels (V25, AlphaGUT, Level) |
| `Hodge/` | 9 | Hodge involution (Core, Star, Delta, Involution{,Capstone}, Prop{,50,52,53,54}) |
| `Universal/` | 8 | Universal property (Core, Prop{,31,41,42,51,52,53}) |
| `Dyadic/` | ~120 | Dyadic FSM family (8 sub-sub-clusters) |
| └─ `Dyadic/ArithFSM/` | 34 | ArithFSM (V1-V3 variants + Mod{N} primes 5..101) |
| └─ `Dyadic/BitFSM/` | 3 | BitFSM helpers (Bound, Converse, Examples) |
| └─ `Dyadic/Pell/` | 17 | Pell-CRT framework |
| └─ `Dyadic/Fib/` | 11 | Fibonacci predictor |
| └─ `Dyadic/Trib/` | 6 | Tribonacci CRT |
| └─ `Dyadic/Legendre/` | 5 | Legendre symbol + V213, V13_19 |
| └─ `Dyadic/Pisano/` | 9 | Pisano predictors (4..22 prime evidence) |
| └─ `Dyadic/Archive/` | 3 | Exploratory historical (Capstone, EdgeSignature, SubwordComplexity) |

## Files at root (~25, framework / utilities)

K5.lean, AlphaEMBridge, Audit, BettiKernel, ClosureExtension,
DiamondAudit, DiamondShape, EncodingBijection, EncodingBijection52,
EulerClosed, LeibnizFinding, Paper1Chiral, Real213Bridge,
SimplexBasis, TopologyCompare, TrivialCases, WhyDimFive,
XorPairCombine

## Naming conventions

- **Core.lean** — namespace anchor (was bare ClusterName.lean)
- **V{digit}.lean** — versioned variants (Lean module names cannot
  start with a digit; V prefix added: V213, V25, V32, V4Capstone, ...)
- **Mod{N}.lean** — arithmetic modulus N variants (Mod7, Mod11, ...)

## See also

- `INDEX.md` — this file
- `../INDEX.md` (lean/E213/INDEX.md) — full library map
- `STRICT_ZERO_AXIOM.md` (root) — strict-0-axiom achievements
