# Atoms Handoff — 2026-04-15

## 현재 상태: Lagrange Coupling Constraint 탐색 중

### 핵심 문제
Regge action만으로는 coupling constant alpha를 결정할 수 없다.
Binet-Cauchy channel 구조를 action에 통합하는 S_total이 필요.

---

## 시도한 접근과 결과

### 접근 1: Lagrange multiplier (직접적)
```
S_total = Sum_h sqrt(det(G_h)) * delta_h + lambda * [R(G) - r_0]
```
R(G) = channel ratio functional, r_0 = 12/25.

변분 delta S/delta psi_i = 0 하면:
- 첫째 항: Regge equation (deficit angle 최소화)
- 둘째 항: channel ratio를 r_0로 고정하는 "gauge force"

**결과**: R(epsilon) ~ 12/13 ~ 0.923, epsilon에 거의 무관.
12/25 = 0.48에 도달 불가. 원인은 R이 hinge 위상에 의해 결정되고
epsilon은 O(epsilon^2) 보정만 주기 때문.

### 접근 2: Channel-weighted Regge action
```
S_total = Sum_h [w_S * det_SSS(h) + w_M * (det_SST(h) + det_STT(h))]^(1/2) * delta_h
```
lambda 불필요하나, weight w_S, w_M 정당화 별도 논리 필요.

### 분석적 결과
- **AAB hinge에서 SSS leakage = epsilon^2 / (1 - 2*epsilon^2)** — exact.
- 모든 ratio 정의가 epsilon의 단조함수 → constraint value를 바꾸면 아무 epsilon 얻음.
- SSS/det = alpha_GUT로 놓으면 epsilon ~ 0.152 (alpha의 20.87배).
- SSS/det = alpha^2로 놓으면 epsilon ~ alpha (tautology).

### 왜 막혔는가
Binet-Cauchy 분해는 단일 hinge의 대수적 성질이라 epsilon의 함수로만 표현됨.
**빠진 요소: deficit angle delta_h.**
- delta(AAA) = pi는 epsilon에 무관 (확인됨)
- 그러나 AAB, ABB hinge의 dihedral angle은 epsilon에 의존
- S_Regge의 극값 조건 + channel ratio 조건이 epsilon에 대해
  독립적 두 방정식이면 epsilon = alpha가 유일 해로 결정 가능

---

## 다음 단계 (새 수학 필요)

### 즉시 해볼 것
1. **2-simplex manifold에서 AAB/ABB hinge의 dihedral angle을 epsilon의 함수로 계산**
   - 이것이 빠진 퍼즐 조각
   - delta(epsilon)이 비자명하면 두 독립 방정식 확보

2. **Full Regge action weight sqrt(det) * delta로 channel ratio 재계산**
   - 기존 계산은 sqrt(det)만 사용, delta 미포함
   - Regge action weight 포함 시 결과가 달라질 수 있음

3. **Local vs Global constraint 구분**
   - Global (single lambda): alpha가 universal constant → 물리적으로 자연스러움
   - Local (hinge별 lambda_h): running coupling → renormalization 관점에서 자연스러움

### 장기 과제
- S_total = S_Regge + S_matter 완전 정립
- 변분에서 screening constants 도출
- deficit angle과 channel ratio의 coupled equation system 풀기

---

## 기존 성과 (유지)

### A. Screening Model (ATM_018-022): median 3.5%
- 8개 screening 상수로 Z=1-118 전부 30% 이내
- 76(<5%), 111(<15%), 118(<30%), median 3.5%
- 패턴 매칭이지만 manifold 해석 있음

### B. Manifold Variational (ATM_024-025): delta(AAA) = pi
- 올바른 기하: Delta^4 (5꼭짓점, 3A+2B)
- 2-simplex gauge 연결 -> delta(AAA) = pi 정확히 도출
- IE(H) = Ry, IE(He) = 2Ry(1 - 4*alpha_GUT)
- Li manifold: 4 simplices, screening = temporal 겹침

## Screening Constants (manifold 해석 포함)
```
Cross-pair (다른 심플렉스 쌍 -> 공유 AAB 힌지):
  sigma_cross = 1 - n_S/(d^2 - 1) = 7/8 = 0.875

Same-pair (같은 심플렉스 -> Binet-Cauchy):
  sigma_same_s = 1/n_T + c^2 * alpha_GUT = 0.597

Subshell:
  sigma_ns->np(even) = 1 - n_S/(d(d-1)) = 17/20
  sigma_ns->np(odd)  = 1 - n_T/(d(d-1)) = 9/10
  sigma_same_p(p=2) = n_S/(n_S+1) = 3/4
  sigma_same_p(p>=3) = n_T/(n_T+1) = 2/3
  sigma_df->p = 1 - alpha_GUT = 0.976
  Delta_pair = n_S/pi^2 = 3/pi^2
```

## Experiment Map
```
ATM_014-016: He, screening analysis, Period 2 complete
ATM_017: Full periodic baseline (26.1%)
ATM_018: sigma_core = 27/10 (6/6)
ATM_019: sigma_df = 1 - alpha_GUT (5/5)
ATM_020: Layered shell (4/4, 7.4%)
ATM_021: Filling fraction (4/4, 3.8%)
ATM_022: d-pair (4/4, 3.5%)
ATM_023: 폐기 (틀린 기하)
ATM_024: Delta^4 single (5/5, delta=3pi/2)
ATM_025: 2-simplex manifold (3/4, delta=pi)
Next: ATM_026
```
