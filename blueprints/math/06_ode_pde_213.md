# Differential Equations 213 — Blueprint

**Priority**: ★★ (applied extension of Analysis 213)

---

## 1. Why This Field

ZFC differential equations:
- ODE: y' = f(t, y), initial value problem
- PDE: ∂u/∂t = Δu (heat), □u = 0 (wave)
- existence/uniqueness (Picard-Lindelöf)

Analysis 213 already covers:
- linear ODE y' = a propEq (Phase CU)
- 2nd-order ODE y'' = 0 (Phase CW)
- Newton's 1st and 2nd laws (Phase CX, DB)

Extension areas:
- general 1st-order nonlinear ODE
- general 2nd-order (harmonic oscillator)
- PDE (heat, wave, Laplace)
- existence theorem

## 2. 213-native Emergence

### 2.1 ODE = IsAntiderivative

Already formalized.  y' = f(y) → y is antiderivative of f.  Linear
case from Phase CU is propEq.  General nonlinear uses cohomEquiv.

### 2.2 Picard iteration (constructive existence)

y_{n+1}(t) = y_0 + ∫_0^t f(s, y_n(s)) ds.

213-native: iterative cut sequence.  Cauchy form.
Picard theorem = Cauchy convergence (Analysis 213 already has the framework).

### 2.3 PDE = multivariable cohomology

Heat: ∂u/∂t = ∂²u/∂x².  213-native:
- Multivariable IsDifferentiable (blueprint 02)
- partial equality (cohomological)

Wave: ∂²u/∂t² = c²∂²u/∂x².  Similar.
Laplace: Δu = 0 = harmonic.

### 2.4 Harmonic oscillator (sin/cos)

y'' = -y → y = sin(t) or cos(t).
Requires extension of transcendental 213 (Analysis 213's sin/cos at 0).

### 2.5 Numerical methods (Euler, RK4)

Discretization itself is dyadic — 213-native.  Bisection step =
dyadic Euler step.

## 3. Building Blocks

| Tool | Use |
|---|---|
| Analysis 213 linear ODE | y' = a (Phase CU) |
| Analysis 213 2nd-order ODE | y'' = 0 (Phase CW) |
| `IsAntiderivative` | nonlinear y' = f(y) |
| `partialSum` | Picard iteration |
| `MultiCut` (blueprint 02) | PDE multivariable |
| `expTermsAtZero` | exp solution to y' = y |

## 4. Phase Plan

### Phase ODA — Picard iteration framework (3-5 commits)

1. Define `picardIterate y_0 f n`
2. Convergence via Cauchy
3. Existence: y' = f(y), y(0) = y_0 → solution exists
4. Uniqueness: Lipschitz f → unique

### Phase ODB — Specific ODE solutions

1. y' = y (exponential) → y = e^t
2. y'' = -y (harmonic) → y = a sin t + b cos t
3. y'' = y (hyperbolic) → y = a sinh t + b cosh t
4. Each via series form propEq at 0

### Phase ODC — PDE foundations

1. Heat equation 1D + initial condition
2. Wave equation 1D + d'Alembert formula
3. Laplace equation in 2D + harmonic

### Phase ODD — Numerical

1. Euler method = dyadic step
2. Convergence rate via linearityModulus
3. RK4 generalization

### Phase ODE — Capstone

First year undergraduate differential equations + PDE foundations.

## 5. Connections to Other Tracks

- **Yang-Mills**: gauge equation = PDE
- **Cosmology**: Friedmann equation (ODE)
- **Quantum gravity**: Einstein equation
- **Atoms**: Schrödinger equation (PDE)
- **DHA**: Fourier method for PDE

## 6. Open Problems

- **Navier-Stokes** — ns-nogo track already in progress
- **Black-Scholes** — finance application
- **Bessel function** — series form
- **Wave on sphere** — multivariable + cohomology

## 7. Key Insights (★)

★ **ODE solution = Cauchy limit of Picard iteration** — 213-native.

★ **PDE = multivariable cohomological** — application of Stokes' theorem.

★ **Numerical method = dyadic step** — discretization natural.

## 8. First Marathon Command

```
"Start Phase ODA.  picardIterate framework + existence on small interval"
```

