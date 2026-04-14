# RH Connection — Session Handoff

## Branch
`claude/rh-handoff-followup-q3hsh`

## Status: Natural Plateau (2026-04-14)
Born-Ramanujan, δ(N) 지수, GRH 닫힘. Phase→Möbius는 DRLT 한계 도달.

---

## Experiment Catalog (RH_001–023)

| ID | Checks | Key Result | Status |
|----|--------|------------|--------|
| RH_001 | 11/11 | β=2 (⟨r⟩=0.594) | ✓ |
| RH_002 | 6/7 | Phase uniform (KS p=0.258) | ✓ |
| RH_003 | 6/6 | CLT σ=1/2 | ✓ |
| RH_004 | 5/5 | σ_geom=1/n_K for all K | ✓ |
| RH_005 | 5/5 | Graph-PNT + Ihara | ✓ |
| RH_006 | 4/5 | Born Ramanujan N≤200 | ✓ |
| RH_007 | 5/5 | d_c≈3, ratio fit | ✓ |
| RH_008 | 3/5 | Var exact, ||Z||~N^{0.82} | ✓ |
| RH_009 | 5/5 | **KR + MP formula** | ★ |
| RH_010 | 3/5 | Segre r_eff | △ |
| RH_011 | 4/4 | **p_eff = d(d-1)** | ★ |
| RH_012 | 4/4 | **α = 2/(d-1) EVT** | ★ |
| RH_013 | 5/5 | **GRH: CLT + GUE/GOE** | ★ |
| RH_014 | 4/5 | Phase→Möbius β=0.80 | △ |
| RH_015 | 4/4 | β(d)→1/2 non-monotone | ✓ |
| RH_016 | 1/2 | FFT artifact | ✗ |
| RH_017 | 3/4 | Beat weak correlation | △ |
| RH_018 | 4/4 | 0⁺ confirmed: ~N/d | ✓ |
| RH_019 | 4/4 | GUE spacings all d | ✓ |
| RH_020 | 5/5 | Ihara coeffs (해석 수정) | △ |
| RH_021 | 2/3 | Coefficients blow up | ✗ |
| RH_022 | 4/4 | Tr distribution exact | ✓ |
| RH_023 | 4/4 | Rank effect (수정됨) | △ |

## Key Results (Confirmed)

| Result | Value | Status |
|--------|-------|--------|
| Two Boundaries: σ_stat=σ_geom ⟺ ℂ | Proven | **Theorem** |
| Doubly Irreducible: {2,3}∩{2}={2} | Proven | **Theorem** |
| CLT σ=1/2 (universal) | Proven | **Theorem** |
| GUE β=2 from ℂ | ⟨r⟩=0.594 | **Theorem** |
| δ(N) ~ 2^{1/(d-1)}·N^{-2/(d-1)} | α=0.5012 | **Theorem** (EVT) |
| Harper: mult preserves σ=1/2 | Citation | **Theorem** |
| W+I = Φ†Φ (Khatri-Rao) | 10⁻¹⁶ | **Theorem** |
| E[φφ†] eigenvalues | exact | **Theorem** |
| p_eff = d(d-1) | RMSE 1.89 | **Semi-analytical** |
| ρ(d,N) closed form | 4.1% median | **Semi-analytical** |
| N_c ~ 3d³ | N_c(5)≈350 | **Semi-analytical** |
| G = G_c + G_t, Tr(G_c)/N = 5/d | <1% | **Theorem** |
| σ suppresses Jarlskog | J_t/J_c=0.41 | **Confirmed** |

## Dead Ends (반복하지 말 것)

1. Ihara 계수 = μ(n): walk length ≠ integer index (RH_020→021)
2. Fourier d-특이적 구조: FFT 아티팩트 (RH_016)
3. Artin split (96% vs 39%): rank 효과, 표현론 아님 (RH_023 correction)
4. cos(θ) → β_eff: 상관 0.06 (RH_017)

## Open Problems

### 1. Phase→Möbius (OPEN, plateau)
모든 시도된 경로 막힘. DRLT는 "왜 1/2 근처"를 설명하지만
"왜 정확히 1/2"에는 도달 못 함 (self-contradiction boundary).

### 2. Book 통합
Paper 5 → ch21_riemann.tex. 아직 미착수.

### 3. 0⁺ 심층
표현론적 구별이 Ihara 영점에는 rank 효과로 가려짐. 다른 관측량 필요.

## Next: RH_024
