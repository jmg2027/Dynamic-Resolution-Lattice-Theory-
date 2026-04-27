# Complex Analysis 213 — Blueprint

**Priority**: ★★ (CayleyDickson track already in place)

---

## 1. Why This Field

ZFC complex analysis:
- ℂ = ℝ + iℝ, |i² = -1|
- holomorphic = complex differentiable
- Cauchy-Riemann equations, residue, contour integral

Natural emergence in 213:
- **CayleyDickson track** already formalized: ZI, ZSqrt2, ZOmega,
  Cayley/Sedenion/Pathion/Trigintaduonion (29 files)
- **Analysis 213** single-variable differentiation framework
- Combining both → 213-native complex analysis

## 2. 213-native Emergence

### 2.1 ℂ as Cayley-Dickson on Cut

```
ComplexCut := Cut × Cut    -- (real, imaginary) pair
def cAdd (z w : ComplexCut) := (z.1 + w.1, z.2 + w.2)
def cMul (z w : ComplexCut) := (z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1)
```

Lift to Cut over `ZI.lean` (already in hand).

### 2.2 Holomorphicity — Cauchy-Riemann

f : ℂ → ℂ holomorphic ↔ ∂u/∂x = ∂v/∂y, ∂u/∂y = -∂v/∂x.

213-native:
- IsDifferentiable (real part), IsDifferentiable (imag part)
- Partial derivatives via multivariable 213 (blueprint 02)
- Cauchy-Riemann = partial equality propEq

### 2.3 Power series + analytic functions

f(z) = Σ aₙ zⁿ.  Combine Analysis 213 series + cutPow.

Complex polynomials: `cMul` chain.  exp(z), sin(z), cos(z), log(z) =
ℂ-lift of Real213 series.

### 2.4 Residue + contour integral

Contour = closed dyadic path on ℂ.  Integral = sum of fluxAlong
each segment.  Residue = limit of (z-a)·f(z) as z → a.

## 3. Building Blocks

| Tool | Use |
|---|---|
| `Real213.CayleyDickson.ZI` | Z[i] = Gaussian integers |
| `Real213.IsDifferentiable` | real/imag part |
| `Real213.cutPow x n` | z^n via cMul chain |
| `Real213.expTermsAtZero` | exp(z) at 0 (sin, cos automatic) |
| `MultiCut 2` | (real, imag) tuple = ℂ point |
| `FluxCut` | contour 1-cochain |

## 4. Phase Plan

### Phase CXA — ComplexCut foundations (3-5 commits)

1. `ComplexCut := MultiCut 2` (multivariable 2 of Real213)
2. Define `cAdd`, `cMul`, `cConj` + associative/commutative propEq
3. `i := (0, 1)`, `i² = -1` propEq
4. `|z|² = z·conj z` (real part)

### Phase CXB — Holomorphic

1. `IsHolomorphicAt f z` via Cauchy-Riemann (partial equality)
2. `id` (z ↦ z) holomorphic
3. `cutPow z n` holomorphic (polynomial = entire)
4. Sum / product / composition holomorphic

### Phase CXC — Series + transcendentals

1. `cExp` via series (ℂ-lift of Analysis 213 exp pattern)
2. `cSin`, `cCos` from cExp
3. Euler's identity: e^(iπ) + 1 = 0 (topological insight, may be hard to formalize)
4. cExp(0) = 1 (definite propEq)

### Phase CXD — Contour integral

1. Define closed dyadic contour
2. `contourIntegral f path`
3. Cauchy's integral theorem (analytic f → ∮ f = 0)
4. Residue theorem skeleton

### Phase CXE — Capstone

First year undergraduate complex analysis.

## 5. Connections to Other Tracks

- **CayleyDickson** (already in hand): ZI, ZSqrt2, etc.
- **Critical Line / RH**: zeta function = complex analysis
- **Yang-Mills**: complex action e^(iS)
- **Quantum Gravity**: complex amplitudes
- **r5-critique**: critique of ℝ-algebra assumption (true nature of complex)

## 6. Open Problems

- **Riemann mapping theorem** — 213-native?
- **Zeta function continuation** — analytic continuation
- **Quaternion / Octonion** transformation (using Cayley-Dickson tower)

## 7. Key Insights (★)

★ **ℂ = Cut × Cut** — direct lift of Analysis 213.

★ **Holomorphic = Cauchy-Riemann partial equality** — directly
formalized by the multivariable 213 framework.

★ **CayleyDickson track in use** — 29 files already in hand,
natural generalization from ℂ → ℍ → 𝕆.

## 8. First Marathon Command

```
"Start Phase CXA.  ComplexCut + cAdd/cMul/cConj + i² = -1 propEq"
```

