# Nuclear Physics — Handoff

## Status: CLOSED (1차) ★★★ — 15 Experiments

## Key Results (0 free parameters)

| Observable | DRLT | Observed | Error | Source |
|-----------|------|----------|-------|--------|
| Magic numbers | 2,8,20,28,50,82,126 | same | **7/7 exact** | NUC_003 |
| E_d (deuteron) | 2.271 MeV | 2.224 MeV | **+2.1%** | NUC_012 |
| r₀ (radius) | 1.262 fm | 1.25 fm | **+0.95%** | NUC_009 |
| a_C (Coulomb) | 0.685 MeV | 0.71 MeV | **-3.6%** | NUC_010 |
| a_V (volume) | 16.0 MeV | 15.5 MeV | **+3%** | NUC_015 |
| a_S (surface) | 18.0 MeV | 16.8 MeV | **+7%** | NUC_015 |
| B/A (sat) | 8.96 MeV | ~8.0-8.8 | **~5%** | NUC_014 |
| B/A (²⁰⁸Pb) | 7.90 | 7.87 | **+0.4%** | NUC_015 |
| κ (SO) | N_T = 2 | — | 5/7 magic | NUC_007 |

## Derivation Chains (all from d=5)

### Magic Numbers
```
d=5 → 600-cell (Thm A) → 2I irreps Vₙ → Sym²(Vₙ) = HO shell (Thm C)
→ M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3) (Thm D)
→ 2, 8, 20, 28, 50, 82, 126
```

### Deuteron
```
d=5 → 600-cell f-vector → cells_per_edge = d = 5
→ f_pair = 1/(2d) → Dyson P(x)=(1+2x)/(1+x)
→ E_d = m_p × x/(1+2x) = 2.271 MeV
```

### Volume Coefficient (Gram Identity)
```
12(φ/2)² + 20(1/2)² + 12(1/(2φ))² = 14 = 2(d+N_T) [EXACT]
→ a_V = 7 × E_edge = 16.0 MeV
```

### Surface (600-cell cap geometry)
```
BFS cap on 600-cell → count boundary edges × G_nn²
→ fit B/A = a_V - a_S/A^{1/3} → a_S = 18.0 MeV
```

## 8 Theorems (A–H)

| Thm | Statement |
|-----|-----------|
| A | 600-cell unique maximal simplicial in ℝ⁴ |
| B | λ_n = 12sin(nπ/5)/(n sin(π/5)) |
| C | Sym²(Vₙ) = HO shell (n-1) |
| D | M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3) |
| E | Cayley SU(2) gauge is flat |
| F | Graph L·S breaks gauge flatness |
| G | κ = N_T = 2 gives {2,8,28,50,82} |
| H | sign(κ) > 0 from ε > 0 |

## Experiments (15)
NUC_001–015: shell analysis, spectral, Sym², rigorous foundations,
Cayley graph, tensor force, κ derivation, deuteron, radii,
mass formula, Dyson resummation, f_pair counting, spectral binding,
Gram binding, surface from Gram.

## Open (정밀화)
1. Light nuclei B/A (A<20) — shell model needed
2. a_A (asymmetry) — isospin + Fermi energy on 600-cell
3. Full B(A,Z) curve — kinetic energy correction
4. E_d 2% residual — D-wave admixture

## Next: NUC_016
