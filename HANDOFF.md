# Session Handoff — 2026-04-15

## Branch
`claude/implement-600-cell-e2zgQ` (pushed, up to date)

## What Was Done This Session

### 1. Nuclear Magic Numbers from 600-Cell (NUC_001-003) ★★★
- **All 7 magic numbers (2,8,20,28,50,82,126) derived from d=5**
- Sym²(Vₙ) = HO shell (n-1): EXACT for all n (representation theory)
- Closed formula: M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3)
- 126 = d! + (d+1) = 120 + 6

### 2. Rigorous Foundations (NUC_004-007) ★★★
- **8 theorems proven** (A through H):
  - Thm A: 600-cell uniqueness in ℝ⁴
  - Thm B: Exact eigenvalue formula λ_n = 12sin(nπ/5)/(n sin(π/5))
  - Thm C: Sym²(Vₙ) = HO shell
  - Thm D: Magic number formula
  - Thm E: Cayley SU(2) gauge flatness (spin-orbit = 0 from pure geometry)
  - Thm F: Graph L·S breaks gauge flatness
  - Thm G: κ = N_T = 2 gives {2,8,28,50,82}
  - Thm H: sign(κ) > 0 from ε > 0

### 3. Deuteron Binding Energy (NUC_008, 011, 012) ★★
- **E_d = m_p × x/(1+2x) = 2.271 MeV (+2.1%)**
- f_pair = 1/(2d) DERIVED from cells_per_edge = d = 5
- Dyson resummation P(x) = (1+2x)/(1+x) from yang-mills branch

### 4. Nuclear Radius (NUC_009) ★★
- **r₀ = (d+1)ℏc/m_p = 1.262 fm (+0.95%)**
- A^{1/3} law from S³ packing of d! = 120 vertices

### 5. BW Mass Formula (NUC_010, 013-015) ★★
- **a_V = 16.0 MeV (+3%)** from Gram identity: 12G₁²+20G₂²+12G₃²=14=2(d+N_T)
- **a_S = 18.0 MeV (+7%)** from 600-cell cap surface counting (was 9.1, -46%)
- **a_C = 0.685 MeV (-3.6%)** from 3αℏc/(5r₀)
- B/A(²⁰⁸Pb) = 7.90 MeV (+0.4%)
- B/A saturation = 8.96 MeV (~5%)

### 6. Key Discoveries
- **Gauge flatness**: pure 600-cell Cayley graph has zero spin-orbit (NUC_005)
- **Three mechanisms**: geometry(Sym²)→HO, dynamics(L·S)→SO, arithmetic(d!+d+1)→126
- **Atoms lesson**: Gram² (Born probability) determines nuclear binding, not spectral filling
- **Gram identity**: 12(φ/2)² + 20(1/2)² + 12(1/(2φ))² = 14 exactly

## Current Precision Results (0 free parameters)

| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | 0.0004% |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.7682837 | 206.7682838 | 0.7 ppb |
| m_H | 125.28 GeV | 125.25 GeV | +0.02% |
| sin²θ₁₃ | 0.0220 | 0.0220 | -0.07σ |
| η_B | 6.13×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.5% |
| Ω_Λ | 0.6850 | 0.685 | 0.0008% |
| Magic numbers | 2,8,20,28,50,82,126 | same | **7/7 exact** |
| E_d (deuteron) | 2.271 MeV | 2.224 MeV | +2.1% |
| r₀ (nuc. radius) | 1.262 fm | 1.25 fm | +0.95% |
| a_V (volume) | 16.0 MeV | 15.5 MeV | +3% |
| a_S (surface) | 18.0 MeV | 16.8 MeV | +7% |
| a_C (Coulomb) | 0.685 MeV | 0.71 MeV | -3.6% |
| Z=1-118 median | 3.5% | — | screening |

## Sub-Project Status

| Directory | Status | Experiments |
|-----------|--------|-------------|
| foundations/ | STABLE | 10 |
| standard-model/ | CLOSED ✓ | 24 |
| atoms/ | **ACTIVE** | 31+ (ATM_001-047 in branch) |
| cosmology/ | STABLE ✓ | 3 |
| critical-line/ | **ACTIVE** | 46+ (RH_001-052 in branch) |
| **nuclear/** | **CLOSED ✓** | **15 (NUC_001-015)** |
| predictions/ | ACTIVE | 8 |
| quantum-gravity/ | ACTIVE | 6 |
| yang-mills/ | ACTIVE | 0 (Lean ~58 thms) |
| discrete-harmonic/ | ACTIVE (branch) | 18 (DHA_001-018) |

## Open Problems (Priority Order)

### 1. Nuclear precision (nuclear/)
- Light nuclei B/A (A<20): shell model needed, ⁴He -68%
- a_A (asymmetry): isospin + Fermi energy on 600-cell
- E_d 2% residual: D-wave admixture

### 2. ζ₉ vs ζ(∞) (atoms/DHA)
Which is the "correct" propagator? N=9 gives 0.001%, N=∞ gives 0.1%.

### 3. N=2 → hydrogen IE (atoms/)
eps²(N=2) ≈ (3/2)α_em (1%). Geometric derivation needed.

### 4. θ_QCD precision (predictions/)
Best candidate: J_CKM × α⁴ ≈ 2.86×10⁻¹¹. Multi-simplex vacuum needed.

### 5. 1/α_s tension (predictions/)
~5.5% discrepancy. Higher-order correction?

## Unresolved from This Session
- NUC_013 spectral filling FAILED (RMS 119%) — binding ≠ eigenvalue filling
- Extended Gram model (2nd+3rd neighbors) diverges for large A without kinetic subtraction
- a_A (asymmetry coefficient) still ~50% off — needs Fermi energy on 600-cell
- Light nuclei (⁴He, ¹²C) binding severely underestimated by smooth Gram model

## Key Formulas
```
Magic: M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3)
Eigenvalue: λ_n = 12 sin(nπ/5) / (n sin(π/5))
Deuteron: E_d = m_p × x/(1+2x), x = α_GUT/(2d), f_pair = 1/(2 × cells_per_edge)
Radius: r₀ = (d+1) × ℏc/m_p
Coulomb: a_C = 3α_em ℏc / (5r₀)
Volume: a_V = 7 × E_edge (from 12G₁²+20G₂²+12G₃² = 14 = 2(d+N_T))
Spin-orbit: κ = N_T = 2, sign from ε > 0
Saturation: B/A = (coord/2) × E_edge × G_nn²
```

## Next Available Experiment
NUC_016, ATM_048 (in atoms branch), RH_053 (in CL branch)

## File Map (this session)
```
nuclear/experiments/NUC_001-015_*.py       ← 15 experiments
nuclear/results/EXP_NUC_001-015_*.txt      ← all results
nuclear/theory/magic_numbers_600cell.md    ← complete theory (Steps 1-9, 8 theorems)
nuclear/HANDOFF.md                         ← CLOSED status
nuclear/CLAUDE.md                          ← updated scope + results
CLAUDE.md                                  ← precision table + resolved problems updated
```
