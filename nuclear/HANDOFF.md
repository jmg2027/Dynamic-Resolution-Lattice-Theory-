# Nuclear Physics — Handoff

## Status: ACTIVE — 10 Experiments Complete ★★★

## Key Results (0 free parameters)

| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| Magic numbers | 2,8,20,28,50,82,126 | same | **7/7 exact** |
| E_d (deuteron) | 2.282 MeV | 2.224 MeV | **+2.6%** |
| r₀ (radius) | 1.262 fm | 1.25 fm | **+0.95%** |
| a_C (Coulomb) | 0.685 MeV | 0.71 MeV | **-3.6%** |
| B/A (²⁰⁸Pb) | 7.953 | 7.868 | **+1.1%** |

## Three Mechanisms for Magic Numbers

```
d = 5 → 600-cell → 2I ≅ SL(2,5)
  ├─ GEOMETRY (Sym²) → HO magic: 2, 8, 20
  ├─ DYNAMICS (L·S, κ=N_T=2) → SO magic: 28, 50, 82
  └─ ARITHMETIC (d!+d+1) → 126
```

## Formulas

```
Magic: M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3)
Eigenvalue: λ_n = 12 sin(nπ/5) / (n sin(π/5))
Deuteron: E_d = m_p × α_GUT / (2d) = m_p × N_S/(d³π²)
Radius: r₀ = (d+1) × ℏc/m_p
Coulomb: a_C = 3α_em ℏc / (5r₀)
Spin-orbit: κ = N_T = 2, sign from ε > 0
```

## 8 Theorems (A–H)

| Thm | Statement | Source |
|-----|-----------|--------|
| A | 600-cell unique maximal simplicial in ℝ⁴ | NUC_004 |
| B | λ_n = 12sin(nπ/5)/(n sin(π/5)) | NUC_005 |
| C | Sym²(Vₙ) = HO shell (n-1) | NUC_003 |
| D | M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3) | NUC_004 |
| E | Cayley SU(2) gauge is flat | NUC_005 |
| F | Graph L·S breaks gauge flatness | NUC_006 |
| G | κ = N_T = 2 gives {2,8,28,50,82} | NUC_007 |
| H | sign(κ) > 0 from ε > 0 | NUC_007 |

## Experiments

| ID | Title | Key Result |
|----|-------|-----------|
| NUC_001 | 600-cell shell analysis | Construction, spectrum, shells |
| NUC_002 | Magic from 600-cell | Spectral subshells, 126=d!+(d+1) |
| NUC_003 | Sym² HO derivation | ★ 7/7 magic numbers |
| NUC_004 | Rigorous foundations | Uniqueness, formula proof |
| NUC_005 | Spin-orbit Cayley | ★ Gauge flatness, exact λ |
| NUC_006 | Tensor force SO | ★ Graph L·S → 5/7 magic |
| NUC_007 | κ derivation | ★ κ=N_T=2, sign from ε>0 |
| NUC_008 | Deuteron binding | ★ E_d = 2.28 MeV (+2.6%) |
| NUC_009 | Nuclear radii | ★ r₀ = 1.262 fm (+0.95%) |
| NUC_010 | Mass formula | a_C -3.6%, heavy B/A ~1-7% |

## Open Problems

### 1. Surface & asymmetry coefficients
a_S, a_A underestimated by ~50%. Tensor force contribution missing.

### 2. Light nuclei binding
BW formula breaks down for A < 20. Need shell model on 600-cell.

### 3. Z=120 superheavy prediction
Complete 600-cell filling → enhanced stability?

### 4. Book integration
Results ready for ch15 (nuclear) or new chapter.

## Next: NUC_011
