# Critical Line — Session Handoff

## Branch
`claude/critical-line-unification-jA2nL`

## Status: ACTIVE (2026-04-15)
rh-connection + gram-algebra 통합 완료. 7개 따름정리 로드맵 진행 중.

**이전:** rh-connection (PLATEAU) + gram-algebra (NOT STARTED) → critical-line/ 통합

---

## Experiment Catalog (RH_001–025)

| ID | Checks | Key Result | Status |
|----|--------|------------|--------|
| RH_001 | 11/11 | β=2 (⟨r⟩=0.594) | Done |
| RH_002 | 6/7 | Phase uniform (KS p=0.258) | Done |
| RH_003 | 6/6 | CLT σ=1/2 | Done |
| RH_004 | 5/5 | σ_geom=1/n_K for all K | Done |
| RH_005 | 5/5 | Graph-PNT + Ihara | Done |
| RH_006 | 4/5 | Born Ramanujan N≤200 | Done |
| RH_007 | 5/5 | d_c≈3, ratio fit | Done |
| RH_008 | 3/5 | Var exact, ‖Z‖~N^{0.82} | Done |
| RH_009 | 5/5 | KR + MP formula | Done |
| RH_010 | 3/5 | Segre r_eff | Done |
| RH_011 | 4/4 | p_eff = d(d-1) | Done |
| RH_012 | 4/4 | α = 2/(d-1) EVT | Done |
| RH_013 | 5/5 | GRH: CLT + GUE/GOE | Done |
| RH_014 | 4/5 | Phase→Mobius β=0.80 | Partial |
| RH_015 | 4/4 | β(d)→1/2 non-monotone | Done |
| RH_016 | 1/2 | FFT artifact | Dead end |
| RH_017 | 3/4 | Beat weak correlation | Partial |
| RH_018 | 4/4 | 0⁺ confirmed: ~N/d | Done |
| RH_019 | 4/4 | GUE spacings all d | Done |
| RH_020 | 5/5 | Ihara coeffs (해석 수정) | Partial |
| RH_021 | 2/3 | Coefficients blow up | Dead end |
| RH_022 | 4/4 | Tr distribution exact | Done |
| RH_023 | 4/4 | Rank effect (수정됨) | Partial |
| RH_024 | — | Chiral projection | Done |
| RH_025 | 3/3 | δ(N) proof levels (ex-GMA_001) | Done |

## Lean 4 Status
23 theorems, 0 sorry. `lean/PmfRh/` 모듈.

## Dead Ends (반복하지 말 것)
1. Ihara 계수 = μ(n): walk length ≠ integer index (RH_020→021)
2. Fourier d-특이적 구조: FFT artifact (RH_016)
3. Artin split: rank 효과, 표현론 아님 (RH_023)
4. cos(θ) → β_eff: 상관 0.06 (RH_017)

## Roadmap: 7 Corollaries (see theory/roadmap.md)

## Next: RH_026
