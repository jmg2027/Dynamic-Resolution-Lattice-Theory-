# CLAUDE.md — RH Connection Sub-Project

## Overview

DRLT에서 리만 가설(RH)로의 연결을 형식화하는 독립 서브프로젝트.
**Paper 5** (`papers/paper5_critical_line.tex`)에 결과가 정리됨.

**상위 프로젝트:** `../CLAUDE.md` 참조. Book이 single source of truth.

## Authors
- Mingu Jeong (Independent Researcher) — theory originator
- Claude (Anthropic) — mathematical formalization, numerical experiments

## The Complete Chain

**2는 유일한 이중 비가약수 (Doubly Irreducible Number):**
- Additive atoms = {2, 3}, Extension atoms over ℝ = {2}
- {2,3} ∩ {2} = {2} → dim_ℝ(ℂ) = n_T = 2

**Branch A (보편적): 왜 Re(s) = 1/2?**
```
|coefficient| = 1 → CLT: Var = Σ 1/k^{2σ} → σ_stat = 1/2
```

**Branch B (ℂ 고유): 왜 GUE?**
```
ℂ unique → β=2 → GUE → pair correlation = ζ zeros (Montgomery-Odlyzko)
```

**Branch C: 함수 방정식의 1/2**
```
θ(x) = Σ e^{-πn²x} → Mellin → ζ(2s) → s/2 (the "2" = dim_ℝ(ℂ))
```

**통합:**
```
1/2 = 1/n_T = 1/dim_ℝ(ℂ) = 1/c = σ_stat = σ_geom = σ_func
```

**Born-rule Ramanujan:**
```
W_ij = |G_ij|² (no thresholding) → ratio ~ 1.94·d^{-0.67}
d_c ≈ 3, d = 5 > d_c → Ramanujan safe
N ≤ N_c(5) ≈ 500: discrete RH holds (100% Ihara zeros on critical line)
```

## Directory Structure
```
rh-connection/
├── CLAUDE.md              ← 이 파일
├── HANDOFF.md             ← 세션 인수인계
├── rh_exploration.md      ← 탐구 로그 (역사 + raw intuitions)
├── lib/
│   ├── __init__.py
│   └── rh_core.py         ← GUE 분석, spectral gap, ratio statistic
├── experiments/
│   ├── EXP_071_rh_chain.py          ← 11/11 ✓ (β=2, δ(N), chain)
│   ├── EXP_071b_phase_structure.py  ← 6/7  ✓ (phase uniform, interference)
│   ├── EXP_071c_clt_boundary.py     ← 6/6  ✓ (CLT σ=1/2)
│   ├── EXP_071d_two_boundaries.py   ← 5/5  ✓ (σ_stat=σ_geom for ℂ only)
│   ├── EXP_071e_ihara_zeta.py       ← 5/5  ✓ (graph-PNT, Ihara zeros)
│   ├── EXP_071f_born_weight_ramanujan.py ← 4/5 ✓ (Born > thresholded)
│   └── EXP_071g_d_dependence.py     ← 5/5  ✓ (d_c≈3, N_c vs d)
├── theory/
│   ├── Doubly_Irreducible.md         ← KEYSTONE: 왜 2인가
│   ├── two_boundries_theorem.md      ← σ_stat=σ_geom ⟺ K=ℂ
│   ├── mobius_randomness.md          ← Master doc (7 thm + 1 conj)
│   ├── ihara_discrete_rh.md          ← 이산 RH on Gram graphs
│   ├── clt_boundary.tex              ← CLT 경계 (수정됨: ℂ 과잉주장 제거)
│   ├── self_contradiction.tex        ← δ(N) > 0 정리
│   ├── z_n_definition.tex            ← Z_N(s) 정의
│   ├── continuous_geometry.tex       ← E_N → M 점근
│   ├── induction_spectral_series.tex ← 귀납 = ζ(s) 부분합
│   └── discrete_calculus.tex         ← 미적분 = G의 사칙연산
├── results/               ← 실험 출력 (7 files)
└── figures/               ← (향후 그래프)
```

## Dependencies
- `../lib/drlt.py` — GramMatrix, D, N_S, N_T, C_LATTICE, ALPHA_GUT, ZETA_2
- `../lib/experiment.py` — Experiment base class
- numpy, scipy

## Experiment Catalog (42/44 checks passed)

| ID | Title | Checks | Key Result |
|----|-------|--------|------------|
| 071 | RH chain | 11/11 | β=2 (⟨r⟩=0.594), δ~N^{-0.505} |
| 071b | Phase structure | 6/7 | Phase uniform (KS p=0.258), 69% cancellation |
| 071c | CLT boundary | 6/6 | σ=1/2 transition, Gram≈Random |
| 071d | Two boundaries | 5/5 | σ_geom=1/n_K exact, only ℂ matches |
| 071e | Ihara zeta | 5/5 | 100% Ramanujan N≤30 (thresholded) |
| 071f | Born weight | 4/5 | 100% Ramanujan N≤200 (Born rule) |
| 071g | d-dependence | 5/5 | ratio~1.94·d^{-0.67}, d_c≈3 |

## Key Precision Results

| Quantity | Value | Source |
|----------|-------|--------|
| β from ℂ⁵ | ⟨r⟩ = 0.594 ± 0.002 (GUE: 0.603) | EXP_071 |
| β from ℝ⁵ | ⟨r⟩ = 0.526 ± 0.002 (GOE: 0.536) | EXP_071 |
| δ(N) exponent | 0.505 (R²=0.9992) | EXP_071 |
| Phase uniformity | KS p=0.258, R=0.008 | EXP_071b |
| Phase entropy ℂ/ℝ | 98.3% / 19.3% | EXP_071b |
| CLT ratio | 0.896 (theory √(π/4)=0.886) | EXP_071c |
| σ_geom(ℂ) | 0.4999 (theory 0.5000) | EXP_071d |
| Ramanujan d_c | ≈ 3 (d=5 safe) | EXP_071g |
| N_c(d=5) | ≈ 500 | EXP_071g |
| ratio fit | 1.94·d^{-0.67}, R²=0.996 | EXP_071g |

## Resolved Problems
1. ~~왜 1/2인가~~ → CLT (보편) + dim_ℝ(ℂ)=2 (Doubly Irreducible)
2. ~~왜 GUE인가~~ → ℂ→β=2 (EXP_071)
3. ~~함수 방정식의 1/2~~ → n²의 "2" = dim_ℝ(ℂ) (Doubly_Irreducible.md)
4. ~~σ_stat=σ_geom 일치~~ → 유일하게 K=ℂ (Two Boundaries Theorem)
5. ~~"1/2 = ℂ에서 온다" 과잉주장~~ → 수정됨: 1/2는 CLT(보편), GUE는 ℂ(고유)

## Open Problems
1. **Phase→Möbius map**: Gram phases → μ(n) 명시적 대응
2. **Multiplicative structure**: Euler product의 곱셈 의존성이 σ_stat=σ_geom를 보존하는가
3. **Born-Ramanujan proof**: ratio < 1 for d≥4를 해석적으로 증명
4. **Higher L-functions**: Dirichlet characters χ(n) ∈ U(ℂ) → GRH 같은 구조?
5. **N_c(d) formula**: N_c ~ C·d^{2/β} 형태의 명시적 공식

## Running Experiments
```bash
cd rh-connection/experiments
python EXP_071_rh_chain.py
python EXP_071d_two_boundaries.py
python EXP_071f_born_weight_ramanujan.py
python EXP_071g_d_dependence.py
```
Next available: EXP_071h

## Paper
`../papers/paper5_critical_line.tex` — 전체 결과 포함
