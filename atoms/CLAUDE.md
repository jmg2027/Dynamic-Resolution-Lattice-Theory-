# Atomic Physics Sub-Project

> **순수 심플렉스 기하학에서 원자 구조를 유도.**
> 기존 화학/물리 프레임(Z_eff, Slater, orbital, Aufbau) 일체 사용 금지.
> Regge action과 Gram determinant만으로 주기율표를 설명.

## 핵심 원칙
1. **δS/δψ = 0 만 사용.** S = Σ_h √det(G_h) × δ_h
2. **screening은 기하학.** σ = 1 - n_X/(geometric dimension) 형태만 허용
3. **"orbital"은 결과.** 심플렉스 기하에서 shell/subshell이 자연스럽게 나와야 함
4. **pair correction은 Basel.** Δ_pair = 3/π² = neutrino와 동일 물리

## 발견된 Screening Constants (전부 d=5에서 유도)

| 상수 | 값 | 공식 | 기하학적 의미 |
|------|-----|------|-------------|
| σ_1s→outer | 7/8 | 1-n_S/(d²-1) | adjoint SU(5) trace |
| σ_same_s | 0.597 | 1/n_T+c²α | BBB channel budget |
| σ_ns→np(even) | 17/20 | 1-n_S/(d(d-1)) | antisymmetric, spatial |
| σ_ns→np(odd) | 9/10 | 1-n_T/(d(d-1)) | antisymmetric, temporal |
| σ_same_p(p=2) | 3/4 | n_S/(n_S+1) | single simplex, spatial |
| σ_same_p(p≥3) | 2/3 | n_T/(n_T+1) | multi-simplex, temporal |
| σ_df→p | 0.976 | 1-α_GUT | **NEW** d/f leaks α_GUT |
| Δ_pair | 0.304 | n_S/π² | 2× neutrino T₂₃ |
| σ_core offset | 27/10 | (d²+n_T)/(d·n_T) | **NEW** pure DRLT |
| σ_core(p≥3) | →1 | 1-n_T²/[d²(n_T-1)+n_T(pd-1)] | Wishart + period |

## 공통 분모 구조
```
d²-1 = 24        → adjoint SU(5): σ_1s, Ξ_confined
d(d-1) = 20      → antisymmetric: σ_ns→np
n_X+1 = 3 or 4   → same-subshell: σ_same_p
d²π² = 25π²      → GUT coupling: σ_df = 1-6/(d²π²)
(d²+n_T)/(d·n_T) → σ_core offset = 27/10
π²               → Basel propagator: Δ_pair
```

## 현재 정밀도

### Period 1-2 (H-Ne): 전부 <3%
| Z | Sym | IE(DRLT) | IE(obs) | Error |
|---|-----|----------|---------|-------|
| 1 | H | 13.606 | 13.598 | +0.1% |
| 2 | He | 24.565 | 24.587 | -0.1% |
| 3 | Li | 5.315 | 5.392 | -1.4% |
| 4 | Be | 9.291 | 9.323 | -0.3% |
| 5 | B | 8.172 | 8.298 | -1.5% |
| 6 | C | 11.021 | 11.260 | -2.1% |
| 7 | N | 14.295 | 14.534 | -1.6% |
| 8 | O | 13.552 | 13.618 | -0.5% |
| 9 | F | 17.159 | 17.423 | -1.5% |
| 10 | Ne | 21.192 | 21.565 | -1.7% |

### Period 3 (Na-Ar): p-block <6%, s-block ~7%
### Period 4 (K-Kr): p-block <3.5%, d-block <10%, median 3.9%
### Period 5 (Rb-Xe): p-block <6%, d-block <11%, median 2.8%
### Period 6 (Cs-Rn): median 12.1% (was 20.6%)
### Period 7 (Fr-Og): median 12.4% (was 35.0%)

### Z=1-118 전체 (ATM_021): 71 (<5%), 108 (<15%), **118 (<30%=100%)**, **median 3.8%**

## Experiment Map
```
ATM_014: He-Li AAB ratio=2(exact), screening σ=7/8 (4/4 ✓)
ATM_015: Period 2 screening decomposition (3/3 ✓)
ATM_016: Period 2 complete, 8/8 <3% (3/3 ✓)
ATM_017: Full periodic Z=1-118, 68/118 <30% (exploratory)
ATM_018: σ_core = 27/10 identification, structural bug fix (6/6 ✓)
ATM_019: σ_df=1-α_GUT, σ_same_p=2/3, 93/118 <30% (5/5 ✓)
ATM_020: Layered shell screening, 115/118 <30%, median 7.4% (4/4 ✓)
ATM_021: Filling fraction, 118/118 <30%, median 3.8% (4/4 ✓)
Next: ATM_022
```

## Open Problems → HANDOFF.md 참조

## Related Legacy Experiments (root experiments/)
```
ATM_001: All elements scan
ATM_002: Simplex atoms
ATM_003: Hydrogen simplex
ATM_004: Bond angles CH₄/NH₃/H₂O (exact ✓)
ATM_005: Clean scorecard
ATM_006: Hydrogen exact
ATM_007: Analytic solutions on ∂(Δ⁵)
ATM_008: Hydrogen variational
ATM_009: Helium analytic
ATM_010: Lithium analytic
ATM_011: Exact closed-form IE
ATM_012: Variational boundary (6/6 ✓)
ATM_013: Helium ionization (5/5 ✓)
```

## Key References
- book/chapters/ch10_atoms.tex — 원자 이론 (6 theorems)
- standard-model/correction_recipes.md — 보정 패턴
