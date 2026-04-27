# Complex Analysis 213 — Blueprint

**우선순위**: ★★ (CayleyDickson 트랙 이미 깔림)

---

## 1. 왜 이 분야인가

ZFC complex analysis:
- ℂ = ℝ + iℝ, |i² = -1|
- holomorphic = complex differentiable
- Cauchy-Riemann eq, residue, contour integral

213 의 자연 등장:
- **CayleyDickson 트랙** 이미 형식화: ZI, ZSqrt2, ZOmega,
  Cayley/Sedenion/Pathion/Trigintaduonion (29 파일)
- **분석학 213** 1변수 미분 framework
- 둘 *결합* → 213-native 복소해석

## 2. 213-native 등장

### 2.1 ℂ as Cayley-Dickson on Cut

```
ComplexCut := Cut × Cut    -- (real, imaginary) pair
def cAdd (z w : ComplexCut) := (z.1 + w.1, z.2 + w.2)
def cMul (z w : ComplexCut) := (z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1)
```

`ZI.lean` (이미 보유) 위에 Cut 으로 lift.

### 2.2 Holomorphicity — Cauchy-Riemann

f : ℂ → ℂ 가 holomorphic ↔ ∂u/∂x = ∂v/∂y, ∂u/∂y = -∂v/∂x.

213-native:
- IsDifferentiable (real part), IsDifferentiable (imag part)
- Partial derivatives via multivariable 213 (blueprint 02)
- Cauchy-Riemann = partial 등식 propEq

### 2.3 Power series + analytic functions

f(z) = Σ aₙ zⁿ.  분석학 213 의 series + cutPow 결합.

복소 다항식: `cMul` chain.  exp(z), sin(z), cos(z), log(z) =
Real213 series 의 ℂ-lift.

### 2.4 Residue + contour integral

Contour = closed dyadic path on ℂ.  Integral = sum of fluxAlong
각 segment.  Residue = limit of (z-a)·f(z) as z → a.

## 3. 빌딩 블록

| 도구 | 활용 |
|---|---|
| `Real213.CayleyDickson.ZI` | Z[i] = ℂ 정수 |
| `Real213.IsDifferentiable` | real/imag part |
| `Real213.cutPow x n` | z^n via cMul chain |
| `Real213.expTermsAtZero` | exp(z) at 0 (sin, cos 자동) |
| `MultiCut 2` | (real, imag) tuple = ℂ 점 |
| `FluxCut` | contour 1-cochain |

## 4. Phase 계획

### Phase CXA — ComplexCut 기초 (3-5 commits)

1. `ComplexCut := MultiCut 2` (Real213 의 다변수 2)
2. `cAdd`, `cMul`, `cConj` 정의 + 결합/교환 propEq
3. `i := (0, 1)`, `i² = -1` propEq
4. `|z|² = z·conj z` (real part)

### Phase CXB — Holomorphic

1. `IsHolomorphicAt f z` via Cauchy-Riemann (partial 등식)
2. `id` (z ↦ z) holomorphic
3. `cutPow z n` holomorphic (다항식 = entire)
4. Sum / product / composition holomorphic

### Phase CXC — Series + transcendentals

1. `cExp` via series (분석학 213 exp 패턴 ℂ-lift)
2. `cSin`, `cCos` from cExp
3. Euler 정리: e^(iπ) + 1 = 0 (위상수학 인사이트, 형식화 어려울 수)
4. cExp(0) = 1 (확실 propEq)

### Phase CXD — Contour integral

1. Closed dyadic contour 정의
2. `contourIntegral f path`
3. Cauchy 적분 정리 (analytic f → ∮ f = 0)
4. Residue theorem skeleton

### Phase CXE — Capstone

학부 복소해석 1년차.

## 5. 다른 트랙 연결

- **CayleyDickson** (이미 보유): ZI, ZSqrt2 등
- **Critical Line / RH**: zeta function = 복소 해석
- **Yang-Mills**: complex action e^(iS)
- **Quantum Gravity**: complex amplitudes
- **r5-critique**: ℝ-algebra 가정 비판 (complex 의 *진짜* 정체)

## 6. 미해결 / Open

- **Riemann mapping theorem** — 213-native?
- **Zeta function continuation** — analytic continuation
- **Quaternion / Octonion** 변환 (Cayley-Dickson tower 활용)

## 7. 핵심 인사이트 (★)

★ **ℂ = Cut × Cut** — 분석학 213 의 직접 lift.

★ **Holomorphic = Cauchy-Riemann partial 등식** — multivariable
213 framework 가 직접 형식화.

★ **CayleyDickson 트랙 활용** — 29 파일 이미 보유, ℂ → ℍ → 𝕆
까지 자연 일반화.

## 8. 첫 마라톤 명령

```
"Phase CXA 시작.  ComplexCut + cAdd/cMul/cConj + i² = -1 propEq"
```

