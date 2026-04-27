# Differential Equations 213 — Blueprint

**우선순위**: ★★ (분석학 213 의 응용 확장)

---

## 1. 왜 이 분야인가

ZFC 미분방정식:
- ODE: y' = f(t, y), 초기치 문제
- PDE: ∂u/∂t = Δu (heat), □u = 0 (wave)
- existence/uniqueness (Picard-Lindelöf)

213 분석학 213 이 이미:
- linear ODE y' = a propEq (Phase CU)
- 2차 ODE y'' = 0 (Phase CW)
- Newton 1, 2 법칙 (Phase CX, DB)

확장 영역:
- 일반 1차 nonlinear ODE
- 2차 일반 (harmonic oscillator)
- PDE (heat, wave, Laplace)
- existence theorem

## 2. 213-native 등장

### 2.1 ODE = IsAntiderivative

이미 형식화 됨.  y' = f(y) → y 가 antideriv of f.  Phase CU 의
linear 경우는 propEq.  일반 nonlinear 는 cohomEquiv.

### 2.2 Picard iteration (constructive existence)

y_{n+1}(t) = y_0 + ∫_0^t f(s, y_n(s)) ds.

213-native: iterative cut sequence.  Cauchy 형식.
Picard 정리 = Cauchy 수렴 (분석학 213 이미 framework).

### 2.3 PDE = multivariable cohomology

Heat: ∂u/∂t = ∂²u/∂x².  213-native:
- Multivariable IsDifferentiable (blueprint 02)
- partial 등식 (cohomological)

Wave: ∂²u/∂t² = c²∂²u/∂x².  비슷.
Laplace: Δu = 0 = harmonic.

### 2.4 Harmonic oscillator (sin/cos)

y'' = -y → y = sin(t) or cos(t).
초월함수 213 (분석학 213 의 sin/cos at 0) 확장 필요.

### 2.5 Numerical methods (Euler, RK4)

Discretization 자체가 dyadic — 213-native.  Bisection step =
dyadic Euler step.

## 3. 빌딩 블록

| 도구 | 활용 |
|---|---|
| 분석학 213 의 linear ODE | y' = a (Phase CU) |
| 분석학 213 의 2차 ODE | y'' = 0 (Phase CW) |
| `IsAntiderivative` | nonlinear y' = f(y) |
| `partialSum` | Picard iteration |
| `MultiCut` (blueprint 02) | PDE multivariable |
| `expTermsAtZero` | exp solution to y' = y |

## 4. Phase 계획

### Phase ODA — Picard iteration framework (3-5 commits)

1. `picardIterate y_0 f n` 정의
2. Convergence via Cauchy
3. Existence: y' = f(y), y(0) = y_0 → solution exists
4. Uniqueness: Lipschitz f → unique

### Phase ODB — Specific ODE solutions

1. y' = y (exponential) → y = e^t
2. y'' = -y (harmonic) → y = a sin t + b cos t
3. y'' = y (hyperbolic) → y = a sinh t + b cosh t
4. Each via series 형식 propEq at 0

### Phase ODC — PDE 기초

1. Heat equation 1D + initial condition
2. Wave equation 1D + d'Alembert formula
3. Laplace equation in 2D + harmonic

### Phase ODD — Numerical

1. Euler method = dyadic step
2. Convergence rate via linearityModulus
3. RK4 generalization

### Phase ODE — Capstone

학부 미분방정식 1년차 + PDE 기초.

## 5. 다른 트랙 연결

- **Yang-Mills**: gauge equation = PDE
- **Cosmology**: Friedmann equation (ODE)
- **Quantum gravity**: Einstein equation
- **Atoms**: Schrödinger equation (PDE)
- **DHA**: Fourier method for PDE

## 6. 미해결 / Open

- **Navier-Stokes** — ns-nogo 트랙 이미 진행 중
- **Black-Scholes** — finance application
- **Bessel function** — series form
- **Wave on sphere** — multivariable + cohomology

## 7. 핵심 인사이트 (★)

★ **ODE 해 = Cauchy 극한 of Picard iteration** — 213-native.

★ **PDE = multivariable cohomological** — Stokes' theorem 의 응용.

★ **Numerical method = dyadic step** — discretization 자연.

## 8. 첫 마라톤 명령

```
"Phase ODA 시작.  picardIterate framework + existence on small interval"
```

