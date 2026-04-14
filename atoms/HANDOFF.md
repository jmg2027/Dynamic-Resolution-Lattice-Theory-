# Atoms Handoff — 2026-04-14

## 현재 상태
- Period 1-2 (Z=1-10): **전부 <3%**, screening 공식 확립
- Period 3 (Z=11-18): **전부 <10%**, σ_core/σ_3s→3p 추가
- Period 4+ (Z=19-118): **58% within 30%**, d/f-block 정밀화 필요

## 이번 세션에서 한 일
1. **ATM_014**: AAB binding ratio=2.0(exact), σ=7/8 확인
2. **ATM_015**: σ 분해 — σ_same_s, σ_2s→2p, σ_same_p 발견
3. **ATM_016**: Period 2 complete (8/8 <3%), σ_same=1/n_T+c²α 발견
4. **ATM_017**: Z=1-118 전체 스캔, d/f-block unified screening

## 핵심 발견
- **σ_same_s = 1/n_T + c²α_GUT** — He correction과 동일 물리 (BBB channel)
- **Δ_pair = 3/π²** — neutrino T₂₃ correction의 2배 (같은 Basel propagator)
- **σ alternation**: n=2는 n_S 사용, n=3는 n_T 사용 → (3,2) split의 직접적 결과
- **d/f electrons = core**: 외부 전자에서 보면 d/f는 core와 구별 불가

## Open Problems (우선순위)

### 1. σ_core(period) 정밀화
현재: σ = 1-n_T/(d²+(p-2.7)d) → 경험적 2.7 제거 필요.
목표: 순수 DRLT 상수로 된 σ_core(p) 공식.
힌트: alkali metal IE에서 역산한 σ 패턴 분석.

### 2. d-block (전이금속) 정밀화
현재: d-electrons을 core처럼 처리 → ±15% 수준.
문제: Sc-Zn에서 σ_d가 σ_core보다 약간 다를 수 있음.
접근: Sc(가장 단순)부터 시작, σ_d 미세조정.

### 3. f-block (란탄족/악틴족) 정밀화
현재: f-electrons도 core처럼 처리 → ±30% 수준.
문제: La-Lu에서 σ_f의 정확한 값.
힌트: f-subshell = 7 states = d+n_T? 기하학적 의미 탐구.

### 4. p-shell half-fill effect 이론화
현재: Δ_pair = 3/π²로 O-F-Ne에서 작동.
문제: 왜 3/π²인가? neutrino와의 연결은 우연인가 필연인가?
접근: BBB hinge의 channel budget 분석.

### 5. 순수 변분 풀이 (장기)
현재: screening 규칙은 "읽는" 것이지 "풀이"가 아님.
목표: δS/δψ=0에서 shell structure가 자동으로 나오는 것.
필요: multi-simplex stacking 이론 (>2 electrons needs >1 simplex).

## 이론 해석 방향

### 오차의 기하학적 해석
현재 모델의 오차(특히 Period 4+)는 **기존 물리 부족이 아니라 기하학 부족**:
- Period 1-2: 단일 심플렉스 ∂(Δ⁵)로 완전 기술 → <3%
- Period 3: 2-simplex stacking 근사 → <10%
- Period 4+: multi-simplex stacking 필요 → 30%+

**오차 = 모자란 심플렉스 수.** 더 많은 전자 = 더 많은 ∂(Δ⁵) 복사본.

### ε leaking과 최소 상호작용 단위
confined quarks의 ε = α^(2/3)(1+α)가 원자 수준에서:
- 전자-핵 coupling ε = Zα/√n_S
- screening σ = 1 - n_X/(geometric dim)
- 이 두 개의 연결: **trace conservation이 screening을 결정**

## File Map
```
atoms/
  CLAUDE.md          ← 프로젝트 개요, screening constants
  HANDOFF.md         ← 이 파일
  experiments/
    ATM_014_he_variational.py      ← 4/4 ✓
    ATM_015_screening_analysis.py  ← 3/3 ✓
    ATM_016_period2_complete.py    ← 3/3 ✓
    ATM_017_full_periodic.py       ← Z=1-118
  results/            ← IE_scan CSV, summary
  scripts/
    periodic_scan.py  ← 기존 scanner (참고용)
  figures/
```

## 다음 실험: ATM_018
