# Session Handoff — 2026-04-14 (Session 2)

## Branch
`main` (all merged)

## What Was Done This Session

### 1. Higgs Quartic λ Derived (EXP_071, 10/10 ✓)
- **Face-level Binet-Cauchy**: Λ⁴(ℂ⁵) = AAAB(4) + AABB(12) = 16 channels
- **Occupation fraction**: f_occ(AABB) = 1/2 = 1/c (self-dual)
- **Scalar vertex dressing**: V(x) = 1+2x (numerator only, no loop)
- **Result**: λ = (1+α_GUT)²/(2c²), m_H = 125.9 GeV (+0.51%)
- Key insight: scalars use vertex factor, fermions use propagator P(x)

### 2. Embedding Correction (EXP_072, 7/7 ✓)
- AABB face = 4/5 simplex vertices → α_eff = α(d-1)/d
- Missing vertex leaks α/d of coupling
- **Corrected**: m_H = v_H(1+α)(1-α/d)/c = **125.28 GeV** (+0.02%, +0.15σ)
- λ = (1+α)²(1-α/d)²/(2c²) = 0.1299
- **Evolution: 3.2% → 0.51% → 0.02%**

### 3. Book & Repo Updated
- ch21_occupation_fraction.tex: quartic theorem + embedding correction
- ch11_mixing.tex: formula + parameter table updated
- lib/drlt.py: higgs_mass() updated
- appendix_verification.tex: 20 experiments, 121/121 checks
- CLAUDE.md: catalog, precision table, resolved problems

## Current Precision Results (0 free parameters)

| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | 0.0004% |
| m_μ/m_e | 206.7682837 | 206.7682838 | 0.7 ppb |
| m_H | 125.28 GeV | 125.25 GeV | **+0.02%** |
| λ (quartic) | 0.1299 | 0.1294 | +0.38% |
| b₂ (1-loop β) | −3.163 | −3.167 | 0.11% |
| IE(He) | 24.565 eV | 24.587 eV | 0.089% |
| sin²θ₁₃ | 0.0220 | 0.0220 | −0.07σ |
| η_B | 6.10e-10 | 6.1e-10 | 0.04% |

## Open Problems (Priority Order)

### 1. Δm_np geometric factor (+11%)
Neutron-proton mass difference has combinatorial overcount.
Need correct geometric form for isospin breaking.

### 2. 1/α₂ weak scale (18.2 vs 29.6)
RGE running from M_GUT to M_Z not yet implemented.
β-function structure derived in EXP_067.

### 3. Neutrino ratio (35% gap)
Democratic seesaw gives 3.73 vs observed 5.71.
Higher-order T-matrix corrections needed.

### 4. 1st gen quark masses
Ξ correction improves leptons but degrades m_u, m_d.
Need confined-specific Ξ formula.

## Next Experiment
EXP_073 (available).

## File Map
```
experiments/EXP_071_higgs_quartic.py       ← 10/10 ✓
experiments/EXP_072_higgs_embedding.py     ← 7/7 ✓
book/chapters/ch21_occupation_fraction.tex ← quartic theorem + embedding
book/chapters/ch11_mixing.tex              ← updated formula + table
lib/drlt.py                                ← higgs_mass() corrected
```
