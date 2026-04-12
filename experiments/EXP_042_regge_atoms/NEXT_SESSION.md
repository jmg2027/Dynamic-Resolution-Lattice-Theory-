# Next Session: EXP_042 Regge Atoms — JAX + Analytical Gradient

## 현재 상태

EXP_042 Phase 1a 완료 (Regge 기계 검증됨):
- SSS det = 1 (정확), SST det = 1-2ε²/3 (6자리 일치)
- 이면각 계산 올바름 (perpendicular projection 방법)
- Regge action S = Σ A_h δ_h 계산 올바름

Phase 1b 미완 (He 정류점 탐색 느림):
- 20-40 DOF에서 Nelder-Mead + 수치 gradient = 타임아웃
- 필요: JAX 자동미분 또는 해석적 gradient

## 다음 세션에서 할 것

### 방법 A: JAX 자동미분

```python
import jax
import jax.numpy as jnp

# Regge action을 JAX-compatible로 재작성
# jax.grad()로 gradient 자동 계산
# → 40-DOF 문제가 초 단위로 수렴

@jax.jit
def regge_action_jax(psi_flat):
    # ... (regge_core.py를 JAX로 포팅)
    return S

grad_S = jax.grad(regge_action_jax)
```

### 방법 B: 해석적 gradient

단일 심플렉스 (5 꼭짓점)에서:
- S = Σ_{10 hinges} A_h × (2π - θ_h)
- A_h = √det(G_3×3) → ∂A/∂ψ 해석적으로 계산 가능
- θ_h = arccos(perp projection) → ∂θ/∂ψ 해석적으로 계산 가능
- Chain rule로 ∂S/∂ψ

### 검증 과제

1. **H (단일 심플렉스)**: Regge 정류점에서 이면각 구조 → E_n = -m_e α²/(n_T n²) 나오는지
2. **He (2 심플렉스, SSS 공유)**: σ = 5/16 나오는지 (정류점의 기하학에서)
3. **H₂O (복수 심플렉스, T 공유)**: cos θ = -1/4 나오는지

### 핵심 주의사항

- **최소화 아님! 정류점 (δS=0) 찾기.** 최소화하면 전부 축퇴함.
- **T를 C²에 구속.** 자유 최적화하면 T가 C³로 가버림.
- **"진공" T₂는 정확히 0이 아님.** 이웃 꼭짓점과 약간 겹침 → 호핑 진폭.

## 파일 위치

```
experiments/EXP_042_regge_atoms/
  regge_core.py          # 현재 Regge 기계 (numpy, 검증됨)
  simplex_builder.py     # 심플렉스 구조 생성
  phase1_verification.py # Phase 1a 완료, 1b 진행중
  phase1b_stationary.py  # 정류점 탐색 (느림, 개선 필요)
```

## 참고: 이미 해석적으로 유도된 결과들

이 실험의 목표는 이 해석적 결과들을 **Regge action에서 수치적으로 재현**하는 것:

| 물리량 | 해석적 | 출처 |
|--------|--------|------|
| σ(1s) | d/c⁴ = 5/16 | compact_stars.tex |
| cos θ(H₂O) | -1/(n_S+1) = -1/4 | water_angle.tex |
| E_n(H) | -m_e α²/(n_T n²) | ch06b_atoms.tex |
| η/s | 1/(c×2π) = 1/(4π) | appendix_qcd.tex |
