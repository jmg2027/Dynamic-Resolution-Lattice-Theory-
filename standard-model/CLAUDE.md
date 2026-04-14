# Standard Model Sub-Project

> SM coupling constants, fermion masses, mixing angles — all derived from d=5.
> 이 디렉토리는 표준 모형 관련 실험과 이론을 모아놓은 곳.

## Scope
- Gauge couplings (α₁, α₂, α₃, α_GUT)
- Fermion masses (quarks, leptons, neutrinos)
- Mixing angles (CKM, PMNS)
- Higgs sector (v_H, m_H, λ)
- n-p mass difference, beta decay

## Key Results (this sub-project, EXP_071-075)

| Observable | DRLT | Observed | Error | EXP |
|-----------|------|----------|-------|-----|
| m_H | 125.28 GeV | 125.25 | +0.02% | 071/072 |
| λ (quartic) | 0.1299 | 0.1294 | +0.38% | 071/072 |
| Δm_np | 1.275 MeV | 1.293 | -1.5% | 073 |
| ν m₃/m₂ | 5.712 | 5.71 | +0.04% | 074 |
| m_u | 2.156 MeV | 2.16 | 0.17% | 075 |
| m_d | 4.661 MeV | 4.67 | 0.19% | 075 |

## Correction Recipes (see correction_recipes.md)
1. **BC level hierarchy**: hinge(gauge) vs face(scalar)
2. **Scalar vs Fermion dressing**: (1+2x) vs P(x)
3. **Embedding correction**: (1-α×miss/d)
4. **EM excess fraction**: (1-S₂/S∞)
5. **Confined Ξ**: α/(d²-1) only (EM terms vanish)

## Experiment Map
```
EXP_071: Higgs quartic λ from face-level BC (10/10)
EXP_072: Higgs embedding correction α/d (7/7)
EXP_073: n-p mass diff EM excess (7/7)
EXP_074: Neutrino ratio T₂₃ Basel correction (5/5)
EXP_075: Confined Ξ for quarks (7/7)
```

## Authoritative Source
All theory → `book/chapters/`. This directory is working space.
