# Atoms Handoff — 2026-04-14 (Session 2)

## 현재 상태
- Period 1-2 (Z=1-10): **전부 <3%**, screening 공식 확립
- Period 3 (Z=11-18): p-block **<6%**, s-block ~9%
- Period 4 (Z=19-36): p-block **<2.5%**, d-block <12%, median 4.7%
- Period 5 (Z=37-54): p-block **<10%**, d-block <8%, median 3.0%
- Period 6-7 (Z=55-118): median 20-35%, σ_core 기울기 보정 필요
- **Z=1-118 전체: 36(<5%), 62(<15%), 93(<30%), median 12.9%**

## 이번 세션에서 한 일
1. **ATM_018**: σ_core offset = (d²+n_T)/(d·n_T) = 27/10 = 2.7 도출
   - "경험적 2.7"이 순수 DRLT 상수임을 증명
   - ATM_017의 구조적 버그 수정 (p-block s-electron 이중 계산)
   - Median: 26.1% → 17.2%
2. **ATM_019**: σ_df = 1-α_GUT + σ_same_p = 2/3 발견
   - d/f 전자가 α_GUT만큼 screening 누출
   - Period 4 p-block: +34% → +2.3% (Ga)
   - Median: 17.2% → 12.9%

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

### 1. σ_core(p) 기울기 보정 (Period 6-7)
현재: σ_core = 1-4/(23+10p) → p≥5에서 기울기 부족.
관측: alkali σ_obs가 모델보다 빠르게 1에 접근.
- p=5: model 0.945 vs obs 0.951 (Rb)
- p=6: model 0.952 vs obs 0.959 (Cs)
- p=7: model 0.957 vs obs 0.967 (Fr)
힌트: layered screening (shell별 다른 σ) 필요. 또는 p² 항?

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
  results/
  scripts/
    periodic_scan.py  ← 기존 scanner
  figures/
```

## 다음 실험: ATM_020
방향: σ_core(p) 기울기 보정. Layered shell screening 또는 p² correction.
