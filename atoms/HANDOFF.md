# Atoms Handoff — 2026-04-15

## 현재 상태 — 두 층위

### 수치 모델 (screening constants, ATM_018-022)
- Z=1-118: 76(<5%), 111(<15%), 118(<30%=100%), **median 3.5%**
- 하지만 이것은 **패턴 매칭**이지 변분 도출이 아님 (아래 참조)

### 변분 풀이 시도 (ATM_023-024)
- ATM_023: **틀린 기하** (6꼭짓점 ∂(Δ⁵)) 사용 → 무의미한 결과
- ATM_024: **올바른 기하** (5꼭짓점 Δ⁴) 사용 → 중요한 발견:
  - S 최대점: ε ≈ 0.059 (α/√3 ≈ 0.004가 아님)
  - He: 두 전자 동일 coupling, screening 미출현
  - **δ(AAA) = 3π/2 (단일 심플렉스) vs 책의 δ(AAA) = π**
  - **결론: 단일 심플렉스로는 수소조차 불가. Manifold 필요.**

## 이번 세션에서 한 일
1. **ATM_018**: σ_core offset = (d²+n_T)/(d·n_T) = 27/10 = 2.7 도출
   - "경험적 2.7"이 순수 DRLT 상수임을 증명
   - ATM_017의 구조적 버그 수정 (p-block s-electron 이중 계산)
   - Median: 26.1% → 17.2%
2. **ATM_019**: σ_df = 1-α_GUT + σ_same_p = 2/3 발견
   - d/f 전자가 α_GUT만큼 screening 누출
   - Period 4 p-block: +34% → +2.3% (Ga)
   - Median: 17.2% → 12.9%
3. **ATM_020**: Layered shell screening model
   - σ(k→n) = 1-n_X/(d²-1+(n-k-1)·d(d+1))
   - Period 6: 20.6% → 12.1%, Period 7: 35.0% → 12.4%
   - La: -2.6%, Ba: +1.2%, U: -2.1%
   - Median: 12.9% → **7.4%**
4. **ATM_021**: Subshell filling fraction
   - σ(n_fill) = σ_shell + (n/N_max)×(σ_df - σ_shell)
   - f-block: Yb +23%→+0.4%, Gd +7%→+0.2%
   - Period 7: 12.4% → 3.1%, actinides 거의 전부 <5%
   - **Median: 7.4% → 3.8%, 118/118 <30%**
5. **ATM_022**: d-block pair correction
   - Δ_d = Δ_pair × (n_d - d)/d for 6 ≤ n_d ≤ 9
   - Ni +16%→+3.3%, Cu +21%→+3.6%, Ag +19%→+4.8%
   - **Median: 3.8% → 3.5%**

## 핵심 발견

### σ_core offset = (d²+n_T)/(d·n_T) = 27/10
```
σ_core(p) = 1 - n_T² / [d²(n_T-1) + n_T(pd-1)]
          = 1 - 4/(23 + 10p)
```
분모: d²(n_T-1) + n_T(pd-1) = {43, 53, 63, 73, 83, 93} for p=2..7

### σ_df = 1 - α_GUT (d/f → p screening)
- d/f 전자 subshell이 정확히 α_GUT = 6/(d²π²)만큼 screening 누출
- gauge coupling과 동일한 물리!
- 기하학: d/f는 outer p-electron에서 거의 완전한 core지만, α_GUT만큼 "보인다"

### Layered shell screening (ATM_020)
```
σ(k→n) = 1 - n_X(k,n) / (d²-1 + (n-k-1)·d(d+1))
  d²-1 = 24  (adjoint, base denominator)
  d(d+1) = 30 (symmetric rep, gap increment)
  n_X = n_S if (k+n) even, n_T if (k+n) odd
  Period 2: σ_core = S_1S = 7/8 (hardcoded, single simplex)
```
σ_eff(p): 0.875, 0.922, 0.936, 0.947, 0.957, 0.965 for p=2..7

### σ_same_p = n_T/(n_T+1) = 2/3 for p≥3
- Period 2: single simplex → n_S/(n_S+1) = 3/4 (spatial sector)
- Period 3+: multi-simplex stacking → n_T/(n_T+1) = 2/3 (temporal dominates)
- 통일 공식: n_X/(n_X+1) where n_X = n_S(p=2) or n_T(p≥3)

## Screening Constants 전체 정리 (8개, 전부 d=5)
```
1. σ_1s→outer   = 1-n_S/(d²-1)        = 7/8    (adjoint)
2. σ_same_s     = 1/n_T+c²α_GUT       = 0.597  (BBB channel)
3. σ_ns→np(even)= 1-n_S/(d(d-1))      = 17/20  (antisym, spatial)
4. σ_ns→np(odd) = 1-n_T/(d(d-1))      = 9/10   (antisym, temporal)
5. σ_same_p(p=2)= n_S/(n_S+1)         = 3/4    (single simplex)
6. σ_same_p(p≥3)= n_T/(n_T+1)         = 2/3    (multi simplex)
7. σ_df→p       = 1-α_GUT             = 0.976  (GUT leaking)
8. Δ_pair       = n_S/π²              = 3/π²   (Basel propagator)
+ σ_core(p)    = 1-4/(23+10p)         for p≥3  (Wishart)
```

## Open Problems (우선순위)

### 1. d-block late elements (Ni, Cu, Ag) regression
ATM_020의 layered model에서 d-block 후반 원소가 악화 (Ni +16%, Cu +21%).
σ_shell(p-1,p)=0.917이 d-shell filling 후반에서 너무 낮음.
힌트: σ_d가 n_d(채워진 수)에 의존? 또는 n_d≥5일 때 σ_df로 전환?

### 2. Period 3 s-block (Na, Mg)
현재: Na -9.4%, Mg -8.0%. σ_core(3) = 0.925 vs alkali σ_obs = 0.916.
힌트: σ_core(3) ≈ 1-n_T/(d²-1) = 11/12 = 0.917이면 Na -1.2%

### 3. d-block 미세조정 (Period 4)
현재: Sc -12%, Ti -11%. σ_core(4) 약간 높음.
개선 방향: d-block 내부의 shell filling 효과.

### 4. f-block 정밀화 (Period 6-7)
현재: ±20-35%. σ_core(6,7) 기울기 문제의 직접적 결과.
σ_core 해결 시 자동으로 개선 기대.

### 5. p-shell half-fill effect 이론화
Δ_pair = 3/π²의 period 의존성? Period 4+에서도 동일한가?

## File Map
```
atoms/
  CLAUDE.md          ← 프로젝트 개요, screening constants
  HANDOFF.md         ← 이 파일
  experiments/
    ATM_014_he_variational.py      ← 4/4 ✓
    ATM_015_screening_analysis.py  ← 3/3 ✓
    ATM_016_period2_complete.py    ← 3/3 ✓
    ATM_017_full_periodic.py       ← Z=1-118 (baseline)
    ATM_018_sigma_core_derivation.py ← 6/6 ✓ (σ_core 도출)
    ATM_019_pblock_precision.py    ← 5/5 ✓ (σ_df, σ_same_p)
    ATM_020_layered_screening.py   ← 4/4 ✓ (layered, median 7.4%)
    ATM_021_filling_fraction.py    ← 4/4 ✓ (filling, median 3.8%)
    ATM_022_dpair_correction.py    ← 4/4 ✓ (d-pair, median 3.5%)
    ATM_023_variational_truth.py   ← 5/5 (틀린 기하! 6꼭짓점)
    ATM_024_correct_geometry.py    ← 5/5 ✓ (올바른 Δ⁴, 중요 발견)
  results/
  scripts/
    periodic_scan.py  ← 기존 scanner
  figures/
```

## 근본적 미해결 문제

### 단일 심플렉스 vs Manifold
ATM_024가 밝힌 핵심: **단일 Δ⁴의 Regge action으로는 원자를 기술할 수 없다.**
- δ(AAA) = 2π - π/2 = 3π/2 (단일) vs δ(AAA) = π (책)
- 책의 δ = π는 **여러 심플렉스가 힌지를 공유**할 때만 가능
- 수소조차도 simplicial manifold가 필요

### Screening의 지위
ATM_018-022의 screening 상수 (7/8, 1-α_GUT 등)는:
- 관측값에서 DRLT 상수를 **패턴 매칭**한 것
- δS/δψ=0에서 **유도되지 않았음**
- 수치적으로 잘 맞지만 (median 3.5%) 이론적 근거 불충분

## 다음 실험: ATM_025
방향: 최소 manifold (2개 심플렉스 sharing AAA face)에서 δ(AAA)=π가 나오는지 확인.
