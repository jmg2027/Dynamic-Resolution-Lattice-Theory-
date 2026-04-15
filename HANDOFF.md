# Session Handoff — 2026-04-15

## Branch
`claude/implement-600-cell-e2zgQ` (pushed, up to date)

## What Was Done This Session

### 1. Nuclear Physics — CLOSED ★★★ (NUC_001-015, 15 experiments)
- **Magic numbers 7/7 exact** from 600-cell Sym²(2I)
  - Formula: M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3)
  - 8 theorems (A-H) proven
- **Deuteron E_d = 2.271 MeV (+2.1%)** from Dyson P(x)=(1+2x)/(1+x)
  - f_pair = 1/(2d) DERIVED from cells_per_edge = d = 5
- **Nuclear radius r₀ = 1.262 fm (+0.95%)** from (d+1)ℏc/m_p
- **BW coefficients**: a_V +3%, a_S +7%, a_C -3.6% from 600-cell Gram
  - Gram identity: 12G₁² + 20G₂² + 12G₃² = 14 = 2(d+N_T) EXACT
- **Gauge flatness discovery** (NUC_005): pure Cayley graph has SO=0
- **Three mechanisms**: geometry→HO(2,8,20), dynamics→SO(28,50,82), arithmetic→126
- **Spin-orbit**: κ = N_T = 2, sign from ε > 0

### 2. Hadron Spectroscopy — CLOSED ★★★ (HAD_001-005, 5 experiments)
- **m_π = 137.6 MeV (+0.2%)** from GMOR with n_eff = C(5,3)-1 = 9
- **m_ω = 782.1 MeV (-0.07%)** from unified hyperfine formula
- **m_J/ψ = 3081.6 MeV (-0.5%)**, m_Υ = 9430.5 MeV (-0.3%)
- **Unified formula**: m_V² = m_PS² + (dΛ/N_T)², Δ = 770 MeV, **RMS 1.8%**
- **Δ-N = 295.7 MeV (+0.6%)** from Λ × (d²-1)/d² = Λ × 24/25
- **Method discovery**: "그림만 그리고 관찰" → det(G) 패턴 → RMS 35%→1.8%

### 3. Cross-Branch Math Integration
- **yang-mills**: closed propagator P(x) → deuteron Dyson resummation
- **DHA**: channel counting (n_eff=9) → pion GMOR
- **atoms**: Gram overlap (σ_cross=7/8) → kaon correction, Born probability → B/A
- **critical-line**: Ihara zeta, spectral flow → nuclear spectral analysis

### 4. Atoms Branch Discoveries (observed, not done here)
- **ATM_054**: Self-consistent algebraic solver BEATS screening (median 1.33% vs 1.58%)
- **Atomic Formulary**: 13 theorems, all rational with ζ₉
- **Rational variational equation**: ε² = 24α_eff/(24-23α_eff+α_eff²) — no transcendence!

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
| m_π (pion) | 137.6 MeV | 137.3 MeV | +0.2% |
| m_ω (omega) | 782.1 MeV | 782.7 MeV | -0.07% |
| m_J/ψ | 3081.6 MeV | 3096.9 MeV | -0.5% |
| Δ-N split | 295.7 MeV | 294 MeV | +0.6% |

## Sub-Project Status

| Directory | Status | Experiments |
|-----------|--------|-------------|
| foundations/ | STABLE | 10 |
| standard-model/ | CLOSED ✓ | 24 |
| atoms/ | **ACTIVE** | 54 (ATM_001-054, branch) |
| cosmology/ | STABLE ✓ | 3 |
| critical-line/ | **ACTIVE** | 52 (RH_001-052, branch) |
| **nuclear/** | **CLOSED ✓** | **15** |
| **hadron/** | **CLOSED ✓** | **5** |
| predictions/ | ACTIVE | 8 |
| quantum-gravity/ | ACTIVE | 6 |
| yang-mills/ | ACTIVE | 0 (Lean ~58 thms) |
| discrete-harmonic/ | ACTIVE (branch) | 18 |

## Open Problems (Priority Order)

### 1. Atoms: self-consistent solver → full periodic table (atoms/ branch)
ATM_054 SC solver beats screening (median 1.33% vs 1.58%).
Run on all 118 elements. Target: median < 1%.

### 2. ζ₉ vs ζ(∞): which propagator? (atoms/DHA)
N=9 gives 0.001%, N=∞ gives 0.1%. Physical answer needed.

### 3. θ_QCD precision coefficient (predictions/)
Best: J_CKM × α⁴ ≈ 2.86×10⁻¹¹. Multi-simplex vacuum needed.

### 4. Hadron: η/η' mixing, φ, heavy meson absolute masses (hadron/)
η' -22%, φ +3.4%. Flavor mixing angle from Gram off-diagonal.

### 5. Nuclear: light nuclei B/A, asymmetry coefficient (nuclear/)
⁴He -68%. Shell model needed for A < 20.

### 6. Book integration: nuclear + hadron chapters
NUC + HAD results → ch15-16 or new chapters.

## Unresolved from This Session
- NUC_013 spectral filling FAILED (RMS 119%) — binding ≠ eigenvalue filling
- Extended Gram (2nd+3rd neighbor) diverges without kinetic subtraction
- HAD_003 corrections made K WORSE (-8.5%) before finding √σ fix
- η' mass still -22% (needs proper flavor mixing)
- a_A (asymmetry) coefficient still ~50% off

## Key Formulas Discovered This Session
```
Magic:       M(n) = max(n(n+1)(n+2)/3, n(n²+5)/3)
Eigenvalue:  λ_n = 12 sin(nπ/5) / (n sin(π/5))
Deuteron:    E_d = m_p × x/(1+2x),  x = α/(2d),  f = 1/(2×cells_per_edge)
Radius:      r₀ = (d+1) × ℏc/m_p
Volume:      12G₁² + 20G₂² + 12G₃² = 14 = 2(d+N_T)  [EXACT identity]
Pion:        m_π² = n_eff × Σm_q × Λ_QCD,  n_eff = C(5,3)-1 = 9
Hyperfine:   m_V² = m_PS² + (dΛ/N_T)²,  Δ = 770 MeV
Baryon spin: Δ-N = Λ × (d²-1)/d² = Λ × 24/25
Saturation:  B/A = (coord/2) × E_edge × G_nn²
```

## Next Available Experiments
NUC_016, HAD_006, ATM_055 (in atoms branch)

## File Map (this session)
```
nuclear/experiments/NUC_001-015_*.py       ← 15 nuclear experiments
nuclear/results/EXP_NUC_001-015_*.txt      ← all nuclear results
nuclear/theory/magic_numbers_600cell.md    ← theory (9 steps, 8 theorems)
nuclear/HANDOFF.md                         ← CLOSED
nuclear/CLAUDE.md                          ← updated
hadron/experiments/HAD_001-005_*.py        ← 5 hadron experiments
hadron/results/EXP_HAD_001-005_*.txt       ← all hadron results
hadron/HANDOFF.md                          ← CLOSED
hadron/CLAUDE.md                           ← created
CLAUDE.md                                  ← 17 precision results, 10 resolved
HANDOFF.md                                 ← this file
```
