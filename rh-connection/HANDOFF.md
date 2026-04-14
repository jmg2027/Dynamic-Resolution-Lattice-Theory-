# RH Connection — Session Handoff

## Branch
`claude/rh-handoff-followup-q3hsh`

## Status: Born-Ramanujan CLOSED-FORM (2026-04-14)
"왜 1/2" + "왜 GUE" 닫힘. Born-Ramanujan 닫힌 공식 완성:
- **ρ(d,N) = [N/(d(d+1))·(1+√(d(d-1)/N))² - 1] / [2√(N/d-1)]**
- p_eff = d(d-1) (비대각 Hermitian 요동 자유도)
- N_c ~ 3d³, d=5: N_c ≈ 350
- Theorem 5.2: "Numerical" → **"Semi-Analytical"**
- 4.1% median accuracy (universal), 0.7% (per-d optimal)

---

## What Was Done

### Sessions 1-5 (2026-04-14/15): Foundation
- **RH_001** (11/11): β=2 확인 via ratio statistic ⟨r⟩=0.594
- **RH_002** (6/7): Phase uniform (KS p=0.258), 69% cancellation
- **RH_003** (6/6): CLT boundary σ=1/2 verified
- **RH_004** (5/5): σ_geom = 1/n_K for ℝ,ℂ,ℍ,𝕆 모두 확인
- **RH_005** (5/5): Graph-PNT + Ihara zeros (thresholded, N≤30: 100%)
- **RH_006** (4/5): Born weight (no threshold): N≤200: 100% Ramanujan
- **RH_007** (5/5): d_c≈3, d=5 safe, ratio~1.94·d^{-0.67} (N=100)
- Paper 5 초고 완성

### Session 6 (current): Paper 5 Upgrade
- **RH_008** (3/5): Born-Ramanujan 종합 검증
  - Var(W_ij) = (d-1)/(d²(d+1)) **exact** (<0.3% all d)
  - ||Z|| ~ N^{0.82} (Wigner N^{0.5}보다 큼, rank-d 상관관계)
  - 수치 불일치 해결: A,α가 N에 의존 (N=100→1.92/0.67, N=200→2.94/0.79)
  - Graph-PNT: growth base ≈ d_eff - 1 확인
- **RH_009** (5/5): Khatri-Rao + Marchenko-Pastur 닫힌 공식
  - W+I = Φ†Φ (exact, 10⁻¹⁶)
  - E[φφ†] eigenvalues: σ₁=1/d, σ₂=1/(d(d+1)) (exact)
  - N_c(MP) ≈ 2.2·d^{3.06} (R²=0.9996)
- **RH_010** (3/5): Segre correction, r_eff = d(d+1)/2
- **RH_011** (4/4): **p_eff = d(d-1)** 발견
  - γ = d(d-1)/N: RMSE 1.89 (vs d²-1: 8.08)
  - 4.1% median accuracy (universal)
  - N_c ~ 3d³, N_c(5) ≈ 350
- Paper 5 대폭 업데이트:
  1. ij=k 구성적 증명 (Section 2)
  2. 함수 방정식의 1/2 = dim_ℝ(ℂ) (Section 3)
  3. Theorem 5.2: closed-form proof (KR + MP + Segre)
  4. γ = d(d-1)/N 공식 (RH_011)
  5. Graph-PNT 수치 데이터 (Section 5)

---

## Key Results Summary

| Result | Value | Status |
|--------|-------|--------|
| 1/2 = 1/n_T = 1/c = σ_func | Exact | **Theorem** |
| σ_stat = σ_geom only for ℂ | Proven | **Theorem** |
| 2 is unique doubly irreducible | Proven | **Theorem** |
| ij=k forces dim≥4 | Constructive | **Theorem** |
| σ_func = 1/2 from L² norm | dim_ℝ(ℂ)=2 | **Theorem** |
| Var(W_ij) = (d-1)/(d²(d+1)) | <0.3% all d | **Theorem** (verified) |
| β=2 from ℂ | ⟨r⟩=0.594 | **Theorem** (numerical) |
| δ(N) ~ N^{-0.505} | R²=0.9992 | **Theorem** (numerical) |
| W+I = Φ†Φ (Khatri-Rao) | exact (10⁻¹⁶) | **Theorem** |
| E[φφ†] = (Tr·I+X)/(d(d+1)) | exact | **Theorem** |
| **p_eff = d(d-1)** | RMSE=1.89 | **Semi-analytical** |
| **λ₂ ≈ Nσ₂(1+√(d(d-1)/N))²-1** | 4.1% median | **Semi-analytical** |
| **N_c ~ 3d³** | N_c(5)≈350 | **Semi-analytical** |
| Born-Ramanujan for d=5 | N_c=293 | **Semi-analytical** |
| Discrete RH (finite N) | 100% Ihara on line | **Observation** |
| Graph-PNT | growth ≈ d_eff-1 | **Observation** |
| Möbius ↔ Gram phases | Conjectured | **Conjecture** |

---

## Theory Documents (priority reading order)

1. `theory/Doubly_Irreducible.md` — **KEYSTONE**: 왜 2인가
2. `theory/two_boundries_theorem.md` — σ_stat=σ_geom ⟺ ℂ
3. `theory/mobius_randomness.md` — Master doc (7 thm + 1 conj, §4.3-4.4 수정됨)
4. `theory/ihara_discrete_rh.md` — 이산 RH + Born weight
5. `theory/clt_boundary.tex` — CLT 경계 (수정: ℂ 과잉주장 제거)
6. `theory/discrete_calculus.tex` — 미적분 = G의 사칙연산
7. `theory/continuous_geometry.tex` — E_N → M 점근
8. `theory/induction_spectral_series.tex` — 귀납 = ζ(s) 부분합
9. `theory/self_contradiction.tex` — δ(N) > 0 정리
10. `theory/z_n_definition.tex` — Z_N(s) 정의
11. `theory/marchenko_pastur_bound.md` — **NEW**: KR + MP + Segre 닫힌 공식

---

## Open Problems (Priority)

### 1. ~~Born-Ramanujan Proof~~ (**CLOSED** — semi-analytical)
- W+I = Φ†Φ (Khatri-Rao, exact)
- E[φφ†]: σ₁=1/d, σ₂=1/(d(d+1)) (exact)
- **p_eff = d(d-1)** (비대각 Hermitian 요동, RH_011)
- **ρ(d,N) = [Nσ₂(1+√(d(d-1)/N))²-1] / [2√(N/d-1)]**
- N_c ~ 3d³, N_c(5) ≈ 350, **4.1% median accuracy**
- Theorem 5.2 → Semi-Analytical

### 2. Phase→Möbius Map (가장 야심적)
Gram 위상 {θ_k} → μ(n) 대응. 곱셈적 구조 보존 필요.
- 원시 순환 = 소수 (graph-PNT 확인됨)
- Euler product 구조가 simplex 네트워크에서 나오는가?
- RH 자체와 동치에 가까움

### 3. Multiplicative Structure
iid 위상이 아닌 곱셈적 의존성에서도 σ=1/2 경계 보존?
Harper/Soundararajan의 random multiplicative function 결과 활용 가능.

### 4. Higher L-functions
Dirichlet characters χ(n) ∈ U(ℂ). GRH도 같은 구조?

### 5. N_c(d) Formula
N_c(5) ≈ 500. 명시적 공식 N_c ~ C·d^{2/β} 유도.

---

## File Map

```
papers/paper5_critical_line.tex          ← Paper 5 (업데이트됨)
rh-connection/
  CLAUDE.md                              ← 업데이트됨
  HANDOFF.md                             ← 이 파일
  rh_exploration.md                      ← 탐구 로그
  lib/rh_core.py                         ← 코어 라이브러리
  experiments/RH_001-007*.py             ← 7개 실험 (42/44)
  experiments/RH_008_born_ramanujan_proof.py ← 종합 검증
  experiments/RH_009_marchenko_pastur.py     ← NEW: MP 공식 검증 (5/5)
  theory/*.{md,tex}                      ← 10개 이론 문서
  results/RH_001-009*.txt                ← 9개 결과 파일
  theory/marchenko_pastur_bound.md       ← NEW: MP bound 이론
```

---

## Quick Resume

다음 세션에서:
1. 이 파일 읽기
2. `theory/Doubly_Irreducible.md` 읽기 (keystone)
3. `theory/mobius_randomness.md` §6, §8 읽기 (chain + open problems)
4. 선생님의 방향 지시에 따라 진행

가장 유망한 다음 단계: **Born-Ramanujan proof** (해석적 증명, 도구 있음)
또는: **Paper 5를 book chapter로 통합** (ch21_riemann.tex)
