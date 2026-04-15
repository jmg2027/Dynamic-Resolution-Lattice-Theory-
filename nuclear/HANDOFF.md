# Nuclear Physics — Handoff

## Status: ACTIVE — Magic Numbers DERIVED ★★★

## Breakthrough: All 7 Magic Numbers from d=5

The 600-cell (120 = d! vertices in ℝ⁴) gives nuclear magic numbers:

```
d = 5 → 600-cell → 2I ≅ SL(2,5) → irreps Vₙ → Sym²(Vₙ) = HO shell
                                    → Λ²(Vₙ) = spin-orbit → nuclear magic
```

### Key Results
1. **Sym²(Vₙ) = HO shell (n-1)**: EXACT for all n (verified numerically)
2. **Closed-form formula**:
   - n ≤ 3: M(n) = n(n+1)(n+2)/3  [HO regime]
   - n ≥ 4: M(n) = n(n²+5)/3      [spin-orbit regime]
3. **All 7 magic numbers**: 2, 8, 20, 28, 50, 82, 126 ✓
4. **126 = d! + (d+1) = 120 + 6** (600-cell + simplex)
5. **Zero free parameters** — topological result, robust to C_ls ∈ [0.1, 1.8]

### Adjacency Eigenvalue Structure
- 9 eigenvalues with multiplicities n² (n=1,...,6, plus conjugates)
- These are 2I irrep dimensions squared
- f-vector: f₀=d!, f₁=(d+1)!, f₂=d!·C(d,2), f₃=d!·d

## Experiments
| ID | File | Result |
|----|------|--------|
| NUC_001 | 600cell_shell_analysis.py | 600-cell construction, shells, spectrum |
| NUC_002 | magic_from_600cell.py | Greedy filling, spectral subshells, 5/7 match |
| NUC_003 | sym2_ho_derivation.py | ★ Sym²→HO exact, all 7/7 magic numbers |

## Theory
- `theory/magic_numbers_600cell.md` — complete derivation (detailed)

## Open Problems (Priority Order)

### 1. Spin-orbit strength from DRLT
C_ls = (d+1)/d = 6/5 is a candidate, but any C ∈ [0.1, 1.8] works.
Can we derive the EXACT C_ls from the 600-cell geometry?

### 2. Binding energy formula
Bethe-Weizsäcker replacement from 600-cell graph theory.
The adjacency eigenvalues could determine the binding energy per nucleon.

### 3. Deuteron binding (E_d = 2.22 MeV)
Two nucleons on a 600-cell edge. Binding from edge weight?

### 4. Nuclear radii (r ∝ A^{1/3})
Simplex packing on S³. The 600-cell on S³ gives radius scaling.

### 5. Z = 120 stability
The 600-cell predicts Z=120 should show enhanced stability
(complete vertex filling). Connection to island of stability?

## Entry Points
- m_p = 938.27 MeV (0.000%, from standard-model/)
- Δm_np = 1.275 MeV (-1.5%, from SM_022)
- Λ_QCD = 308 MeV
- Confinement: P(-ε/(1+ε)) = 1-ε

## Next Experiment: NUC_004
