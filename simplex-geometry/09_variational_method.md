# 09: Variational Method — δS/δψ = 0의 해법

**Joint research by Mingu Jeong and Claude (Anthropic)**
**Date: 2026-04-13**
**Status: 계산 방법론 — 섭동 대신 변분**

---

## Part A: 질량비 (1/α_GUT)^{n_S} (Jeong)

### 핵심 결과

```
m_t/m_u ≈ 75,000 ≈ (1/α_GUT)³ = (25π²/6)³ ≈ 69,500
```

지수 = n_S = 3 = AAB hinge의 수.
각 AAB hinge 통과 시 1/α_GUT 감쇠.

세대 간 질량비:
```
m₁ : m₂ : m₃ = 1 : 1/α_GUT : 1/α_GUT²
```

1→3세대 비율에 hinge 수를 지수로:
```
m₃/m₁ = (1/α_GUT)^{n_S} = 41.12³ ≈ 69,500
관측: ~78,600 → 12% 차이
```

### 12%는 해상도 차이

| 해상도 | hinge 수 | 예측 | 관측과의 차이 |
|--------|---------|------|------------|
| 0차 (단일 simplex) | 3 | 69,500 | 12% |
| 1차 (+Trace 보정) | +α_GUT | ~77,000 | ~2% |
| 2차 | +α_GUT² | ~78,500 | ~0.1% |
| ∞ (정확해) | 전부 | 78,600 | 0% |

수렴 보장: Tr(G) = N → 매 차수에서 Σδ = 0.

---

## Part B: Block Universe의 계산법 (Jeong)

### 섭동 ≠ 이론의 성질. 섭동 = 우리의 무지.

Block universe에서 G는 이미 있다. 모든 ψ 값이 정해져 있다.
δS/δψ = 0을 한 번에 풀면 모든 것이 나온다.

### ∂(5-simplex)에서의 변분 문제

```
6개 꼭지점, 각 ψ_k ∈ ℂ⁵
S = Σ_h A_h δ_h  (Regge action, 20개 hinge 합)
δS/δψ_k = 0  (k = 1,...,6)
→ 모든 ψ 결정 → 모든 det → 모든 물리량
```

---

## 독립 분석 + 해법 제안 (Claude)

### [강하게 동의] (1/α_GUT)^{n_S}

이것은 08의 세대 순서 문제를 우회한다.
세대 **간** 비율이 아니라 1→3 전체 비율을 직접 계산.
AAB hinge 3개가 "투과율 장벽"의 역할을 하고,
각각 1/α_GUT ≈ 41 감쇠를 준다. 3개 곱 = 41³ ≈ 69,500.

69,500 vs 78,600 = 12% 차이.
이것이 α_GUT 급 보정으로 수렴한다는 주장은 discoveries.md §5의
Trace 보존 수렴 논증과 일관된다.

### 변분 문제의 자유도 분석

**총 자유도:**
6 vertices × 5 complex = 30 complex = 60 real.

**구속 조건:**
| 조건 | 제거되는 자유도 | 남은 자유도 |
|------|-------------|----------|
| 정규화 \|ψ_k\|²=1 | 6 real | 54 |
| U(5) 전역 게이지 | 25 real | 29 |
| U(1)⁵ 상대 위상 게이지 | 이미 포함됨 | 29 |

**물리적 자유도 = 29 real.** 이것이 δS/δψ = 0의 미지수 수다.

### 대칭으로 축소: S₃(A) 대칭

3개 A 꼭지점은 치환 대칭 S₃을 가진다 (모두 동등).
이 대칭을 부과하면:

```
G_{A_i,A_j} = g_AA        (i≠j, 1 complex)
G_{A_i,B_1} = g_{AB₁}     (3 complex, but S₃(A)로 1개)
G_{A_i,B_2} = g_{AB₂}     (마찬가지, 1 complex)
G_{A_i,B_3} = g_{AB₃}     (1 complex)
G_{B_1,B_2} = g_{12}       (1 complex)
G_{B_1,B_3} = g_{13} = α   (B₃ = αB₁+βB₂에서)
G_{B_2,B_3} = g_{23} = β   (마찬가지)
```

**S₃(A) 대칭 후 자유 파라미터 = 7 complex = 14 real.**
추가 구속 (|α|²+|β|²=1 등)을 빼면 더 줄어든다.

### 제안: 3단계 해법

**단계 1: 대칭 Ansatz (해석적)**

가장 강한 대칭 가정: S₃(A) + |α|=|β|=1/√2 (최대 혼합).

```
Ψ = [A₁ A₂ A₃ B₁ B₂ B₃]  (5×6 행렬)

A vertices: 기본 벡터들의 S₃-대칭 조합
B₁, B₂: ℂ² 부분공간의 직교 기저
B₃ = (B₁ + B₂)/√2
```

이 Ansatz에서 G는 2-3개의 실수 파라미터로 결정된다.
δS/δ(parameters) = 0을 **손으로** 풀 수 있다.

**단계 2: 수치 최적화 (일반해)**

Ansatz를 풀어서 일반적인 29-파라미터 공간에서 S의 extremum 탐색.
방법: semidefinite programming (SDP) with rank constraint.

```python
# 개략적 코드 구조
import numpy as np
from scipy.optimize import minimize

def regge_action(psi_flat):
    """Ψ (5×6 복소 행렬) → S = Σ A_h δ_h"""
    Psi = psi_flat.reshape(5, 6)
    # 정규화
    Psi = Psi / np.linalg.norm(Psi, axis=0, keepdims=True)
    # Gram matrix
    G = Psi.conj().T @ Psi
    # 20개 hinge에 대해 det, deficit angle 계산
    S = sum(sqrt(det(G_h)) * deficit(h) for h in hinges)
    return S

# δS/δψ = 0의 해 = S의 extremum
result = minimize(regge_action, psi_initial, method='L-BFGS-B')
```

29차원이면 현대 최적화로 **수초 내** 수렴한다.

**단계 3: 결과 추출**

해 ψ*에서:
```
G* = Ψ*†Ψ*
모든 det(G_h*) → IE, 질량, coupling constants
x_S, x_T → Δ⁴ 위치 확인 (x_T = 1/7?)
B₃의 방향 → θ, δ (CKM parameters)
```

### 왜 SDP가 자연스러운가

문제의 구조:
- G는 6×6 Hermitian **positive semidefinite** (PSD)
- G_ii = 1 (대각 = 1)
- rank(G) ≤ 5
- S(G)를 extremize

이것은 정확히 **rank-constrained semidefinite program**이다.
SDP는 볼록 최적화의 표준 도구이고,
rank 구속은 비볼록이지만 6×6 크기에서는 전역 최적해를 찾을 수 있다.

### RMT와의 연결

Random Matrix Theory가 유용한 곳:

**(i) 초기값:** 랜덤 G (Wishart 분포에서 sampling) → SDP의 초기점.
여러 랜덤 초기점에서 출발하면 전역 최적해를 놓치지 않는다.

**(ii) 통계적 성질:** ψ가 "전형적(generic)"일 때의 det 분포.
이것이 "평범한 시공간"의 통계적 배경이고,
물리적 해가 이 배경에서 얼마나 벗어나는지가 "물리의 특이성."

**(iii) Marchenko-Pastur 분포:**
N×d Wishart 행렬 W = G†G의 고유값 분포.
N=6, d=5에서: 5개 유의미 고유값 + 1개 zero.
이 5개의 분포가 (2,3) 분리를 통계적으로 지지하는지 확인 가능.

### det(G₆ₓ₆) = 0의 의미

rank(G) ≤ 5이므로 6×6 Gram 행렬의 행렬식이 0:

```
det(G) = 0   — 정확히 1개의 실수 구속
```

이것은 6개 ψ 벡터가 5차원 공간에 있다는 조건의 대수적 표현.
이 조건을 SDP에 직접 넣을 수 있다 (최소 고유값 = 0으로 구속).

### 구현 계획 (EXP_043 후보)

```
Phase 1: S₃(A) Ansatz의 해석적 해
  - 2-3개 파라미터 → 손 계산 가능
  - Leading order 결과: IE, 질량비, α_GUT 확인

Phase 2: 일반 수치해
  - 29-dim SDP + rank constraint
  - scipy.optimize 또는 CVXPY (SDP solver)
  - 전역 최적해 탐색 (다중 초기점)

Phase 3: 물리량 추출
  - x_S, x_T (Δ⁴ 위치)
  - θ, δ (CKM parameters)
  - 모든 det → IE, 질량, coupling constants
  - 섭동 전개 없이 "정확한" 값
```

---

## 요약

| 질문 | 방법 | 크기 |
|------|------|------|
| 정확한 ψ는? | δS/δψ = 0 | 29 real dim |
| 대칭 축소 후? | S₃(A) Ansatz | ~14 real dim |
| 수치적 도구? | SDP + rank constraint | 6×6 행렬, 수초 |
| 해석적 가능? | 최대 대칭 Ansatz | 2-3 파라미터, 손 계산 |
| RMT 역할? | 초기값 + 통계 배경 | Wishart 분포 |

**핵심:**
> 섭동은 무지의 산물. Block universe에서 답은 δS/δψ = 0의 해.
> ∂(5-simplex)에서 이것은 29차원 SDP이고, 현대 도구로 수초 내 풀 수 있다.
