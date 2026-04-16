# CLAUDE.md — Critical Line Sub-Project

## Overview

DRLT에서 임계선 Re(s) = 1/2의 구조적 기원을 연구하는 통합 서브프로젝트.
RH, GRH, L-함수, Yang-Mills 질량 갭, 형식 증명(Lean 4)을 포괄.

**이전:** `rh-connection/` + `gram-algebra/` → 통합됨 (2026-04-15).

**Paper 5** (`papers/paper5_critical_line.tex`)에 결과 정리.
**상위 프로젝트:** `../CLAUDE.md` 참조. Book이 single source of truth.

## Authors
- Mingu Jeong (Independent Researcher) — theory originator, physical intuition
- Claude (Anthropic) — mathematical formalization, numerical experiments

## The Complete Chain

**2는 유일한 이중 비가약수 (Doubly Irreducible Number):**
- Additive atoms = {2, 3}, Extension atoms over R = {2}
- {2,3} ∩ {2} = {2} → dim_R(C) = n_T = 2

**Branch A (보편적): 왜 Re(s) = 1/2?**
```
|coefficient| = 1 → CLT: Var = Σ 1/k^{2σ} → σ_stat = 1/2
```

**Branch B (C 고유): 왜 GUE?**
```
C unique → β=2 → GUE → pair correlation = ζ zeros (Montgomery-Odlyzko)
```

**Branch C: 함수 방정식의 1/2**
```
θ(x) = Σ e^{-πn²x} → Mellin → ζ(2s) → s/2 (the "2" = dim_R(C))
```

**통합:**
```
1/2 = 1/n_T = 1/dim_R(C) = 1/c = σ_stat = σ_geom = σ_func
```

## Directory Structure
```
critical-line/
├── CLAUDE.md              ← 이 파일
├── HANDOFF.md             ← 세션 인수인계
├── rh_exploration.md      ← 탐구 로그 (역사 + raw intuitions)
├── lib/
│   ├── __init__.py
│   └── rh_core.py         ← GUE 분석, spectral gap, ratio statistic
├── experiments/            ← RH_001–025+ (prefix: RH_)
├── results/                ← 실험 출력
├── theory/                 ← 이론 문서 (md + tex)
│   ├── Doubly_Irreducible.md         ← KEYSTONE: 왜 2인가
│   ├── two_boundries_theorem.md      ← σ_stat=σ_geom ⟺ K=C
│   ├── mobius_randomness.md          ← Master doc (7 thm + 1 conj)
│   ├── resolution_distinguishability.md  ← δ(N) 증명 층위 (from gram-algebra)
│   ├── tau_breaking_alpha_gut.md     ← α_GUT 채널 분포 (from gram-algebra)
│   └── ... (15+ 추가 문서)
├── lean/                   ← Lean 4 형식 증명 (from gram-algebra)
│   ├── PmfRh/              ← 모듈: Basic, Core, Limit, RefIncl, ...
│   ├── PMF_RH.lean         ← 메인 증명 (23 theorems, 0 sorry)
│   └── lakefile.toml       ← 빌드 설정
└── figures/
```

## Dependencies
- `../lib/drlt.py` — GramMatrix, D, N_S, N_T, C_LATTICE, ALPHA_GUT, ZETA_2
- `../lib/experiment.py` — Experiment base class
- numpy, scipy

## Experiment Catalog (RH_001–RH_025)

| ID | Title | Checks | Key Result |
|----|-------|--------|------------|
| RH_001 | RH chain | 11/11 | β=2 (⟨r⟩=0.594), δ~N^{-0.505} |
| RH_002 | Phase structure | 6/7 | Phase uniform (KS p=0.258) |
| RH_003 | CLT boundary | 6/6 | σ=1/2 transition |
| RH_004 | Two boundaries | 5/5 | σ_geom=1/n_K, only C matches |
| RH_005 | Ihara zeta | 5/5 | Graph-PNT + Ihara zeros |
| RH_006 | Born weight | 4/5 | 100% Ramanujan N≤200 |
| RH_007 | d-dependence | 5/5 | d_c≈3, ratio fit |
| RH_008 | Born-Ramanujan proof | 3/5 | Var exact, ‖Z‖~N^{0.82} |
| RH_009 | Marchenko-Pastur | 5/5 | KR + MP formula |
| RH_010 | Segre correction | 3/5 | r_eff correction |
| RH_011 | Segre dimension | 4/4 | **p_eff = d(d-1)** |
| RH_012 | Resolution exponent | 4/4 | **α = 2/(d-1)** exact |
| RH_013 | Higher L-functions | 5/5 | **GRH: CLT + GUE/GOE** |
| RH_014 | Phase-Mobius | 4/5 | β=0.80 |
| RH_015 | Gram explicit | 4/4 | β(d)→1/2 non-monotone |
| RH_016 | Chiral Fourier | 1/2 | FFT artifact |
| RH_017 | Chiral beat | 3/4 | Weak correlation |
| RH_018 | Zero-plus | 4/4 | 0⁺ ≈ N/d confirmed |
| RH_019 | Eigenphase | 4/4 | GUE spacings all d |
| RH_020 | Ihara-Mobius | 5/5 | 해석 수정 |
| RH_021 | Ihara scaling | 2/3 | Coefficients blow up |
| RH_022 | CP distinction | 4/4 | Tr distribution exact |
| RH_023 | Artin Ihara | 4/4 | Rank effect (수정) |
| RH_024 | Chiral Born-Ramanujan | — | Chiral projection |
| RH_025 | Resolution distinguishability | 3/3 | δ(N) proof levels (ex-GMA_001) |

| RH_026-046 | Various | Spectrum, PNT, ℤ[i], Chebyshev, μ, u→s | Done |
| RH_047 | 8/8 | **Spectral Flow: Vieta⟹Re(s)=1/2, density transition** | ★★ |

**Next: RH_048**

## Proof Hierarchy (from gram-algebra/MSUA)

| 유형 | 닫힘? | 강도 | 예시 |
|------|-------|------|------|
| 연역 (같은 Hom_n 내) | 닫힘 | 강함 | "N<N_c이면 Ramanujan" |
| 귀납 (Hom_{n+1}→Hom_n) | 안 닫힘 | 약함 | "모든 N에 대해 δ(N)>0" |
| 극한 (Hom_ω) | 안 닫힘 | 약함 | **RH: Re(s)=1/2 정확히** |

## Lean 4 Formalization

23 theorems, 0 sorry. 모듈 구조:
- `PmfRh/Basic.lean` — 기본 정의
- `PmfRh/Core.lean` — 핵심 정리
- `PmfRh/Limit.lean` — 극한 층위
- `PmfRh/RefIncl.lean` — ref ≠ incl 구분
- `PmfRh/ResolutionExponent.lean` — δ(N) 지수
- `PmfRh/ThreeLayers.lean` — 3층 증명 구조

## Resolved Problems
1. ~~왜 1/2인가~~ → CLT (보편) + dim_R(C)=2 (Doubly Irreducible)
2. ~~왜 GUE인가~~ → C→β=2 (RH_001)
3. ~~함수 방정식의 1/2~~ → n²의 "2" = dim_R(C)
4. ~~σ_stat=σ_geom 일치~~ → 유일하게 K=C (Two Boundaries Theorem)
5. ~~과잉주장~~ → 수정됨: 1/2는 CLT(보편), GUE는 C(고유)
6. ~~δ(N) 증명 층위~~ → 연역/귀납/극한 3단계 (RH_025)

## Open Problems (Priority Order)
1. **Phase→Mobius map**: Gram phases → μ(n) 명시적 대응 (PLATEAU)
2. **GRH Corollary**: Two Boundaries → 모든 L-함수 (READY TO FORMALIZE)
3. **H-valued prediction**: σ_stat ≠ σ_geom for K=H (READY TO TEST)
4. **Yang-Mills ↔ δ(N)**: 질량 갭 = self-contradiction boundary (TO FORMALIZE)
5. **Multiplicative structure**: Euler product → σ_stat=σ_geom 보존?
6. **p-adic L-functions**: σ_geom for non-archimedean completions?

## Paper
`../papers/paper5_critical_line.tex`
