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
| σ_2s→2p | 17/20 | 1-n_S/(d(d-1)) | antisymmetric rep |
| σ_3s→3p | 9/10 | 1-n_T/(d(d-1)) | sector alternation |
| σ_same_p(n=2) | 3/4 | n_S/(d-1) | spatial fraction |
| σ_same_p(n=3) | 2/3 | n_T/n_S | sector ratio |
| Δ_pair | 0.304 | n_S/π² | 2× neutrino T₂₃ |
| σ_core(p≥3) | →1 | 1-n_T/(d²+(p-2.7)d) | Wishart + period |

## 공통 분모 구조
```
d²-1 = 24  → adjoint SU(5): σ_1s, Ξ_confined
d(d-1) = 20 → antisymmetric: σ_ns→np
d-1 = 4    → spacetime: σ_same_p
π²         → Basel propagator: Δ_pair
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

### Period 3 (Na-Ar): 전부 <10%
### Period 4+ (K-Og): 58% within 30%, d/f-block 개선 필요

### Z=1-118 전체: 15 (<5%), 41 (<15%), 68 (<30%)

## Experiment Map
```
ATM_014: He-Li AAB ratio=2(exact), screening σ=7/8 (4/4 ✓)
ATM_015: Period 2 screening decomposition (3/3 ✓)
ATM_016: Period 2 complete, 8/8 <3% (3/3 ✓)
ATM_017: Full periodic Z=1-118, 68/118 <30% (exploratory)
Next: ATM_018
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
