# Multivariable Calculus 213 — Blueprint

**Priority**: ★★★ (direct extension of Analysis 213)

---

## 1. Why This Field

Analysis 213 handles only single-variable (Cut → Cut) functions.
Core of sophomore/engineering calculus:
- partial derivative ∂f/∂xᵢ
- gradient ∇f, divergence ∇·F, curl ∇×F
- multiple integral ∫∫ f dA, ∫∫∫ f dV
- Stokes' theorem (general dimension)

213 already has a *cohomological structure*, so multivariable
may not be very difficult — natural extension of the 1-variable
framework to product spaces.

## 2. 213-native Emergence

### 2.1 Multi-Cut

```
MultiCut n := Fin n → Cut
  -- n-dimensional point = tuple of n cuts
```

Function: `MultiCut n → Cut` or `MultiCut n → MultiCut m`.

### 2.2 Partial derivative

Only the i-th cut varies, rest fixed:

```
def partialAt (f : MultiCut n → Cut) (i : Fin n) (x : MultiCut n)
    : (Cut → Cut) :=
  fun y => f (x.update i y)
```

This is a single-variable function → IsDifferentiable applicable.

### 2.3 Gradient as MultiCut-valued

```
def gradient (f : MultiCut n → Cut) (x : MultiCut n) : MultiCut n :=
  fun i => (partialAt f i x).derivative ?
```

Output is also an n-tuple.  Natural extension to vector calculus.

### 2.4 Divergence + curl via cohomology

213's `localDivergence` is 1-dimensional.  n-dimensional generalization:
```
def divergence (F : MultiCut n → MultiCut n) (x : MultiCut n) : Cut :=
  Σᵢ (partialAt (Fᵢ) i x).derivative
```

= ∑ ∂Fᵢ/∂xᵢ — standard definition.  **Natural generalization of 1D FluxCut**.

### 2.5 Multiple integral via tensor Riemann

```
def riemannMulti (f : MultiCut n → Cut) (db : Fin n → DyadicBracket) (depth : Nat)
    : Cut := Σ over product grid
```

Product of dyadic brackets → multi-dimensional Riemann sum.

## 3. Already-Laid Building Blocks

| Tool | Use |
|---|---|
| `IsDifferentiable f` | applied per partial as single-variable |
| `IsAntiderivative` | iterated integral (Fubini) |
| `FluxCut` | 1D 1-cochain → n-dimensional (n-1)-cochain |
| `dyadicIntervalAB` | n-cube product |
| `cutPow x n` | multivariate polynomial (per variable) |

## 4. Phase Plan

### Phase MA — MultiCut foundations (3-5 commits)

1. `MultiCut n := Fin n → Cut`
2. `MultiCut.update`, `MultiCut.const`, `MultiCut.basis`
3. Vector arithmetic: `multiAdd`, `multiSub`, `multiScale`
4. `unitNCube n` — [0,1]^n product bracket

### Phase MB — Partial derivative

1. Define `partialAt f i x`
2. `IsPartiallyDifferentiable f i` — i-th partial IsDifferentiable
3. `IsCInfDifferentiable f` — all partials differentiable
4. Polynomial partials: ∂(x²y)/∂x = 2xy form propEq

### Phase MC — Gradient + divergence + curl

1. `gradient f` : MultiCut n → MultiCut n
2. `divergence F` : MultiCut n → Cut (sum of partials)
3. `curl F` (n=3) : MultiCut 3 → MultiCut 3
4. Identity: ∇·(∇×F) = 0 (curl of grad is zero)

### Phase MD — Multiple integral

1. `riemannMulti f db_n depth`
2. Fubini propEq: order-independent (special cases first)
3. Iterated `IsAntiderivative` form
4. ∫ const over n-cube = product of edge lengths

### Phase ME — Stokes' theorem (cohomological)

The 1D FTC of Analysis 213 is the *1-d version of Stokes' theorem*.
Natural n-dimensional generalization:
- ∫_M dω = ∫_∂M ω
- 213-native: localDivergence integrated over volume = boundary flux

### Phase MF — Capstone

Core of sophomore calculus / engineering mathematics.

## 5. Connections to Other Tracks

- **Yang-Mills**: 4D ∫ F ∧ *F (= action)
- **Cosmology**: 3+1 dimensional spacetime integration
- **Quantum gravity**: spacetime emergence → multivariable natural
- **Atoms**: Wedge screening = 4D simplex integral
- **DHA**: multivariable Fourier

## 6. Open Problems

- **Coordinate change** (Jacobian) — 213-native?
- **Manifold** definition — what manifold over 213 dyadic?
- **Riemannian metric** — cohomological?
- **Differential form** general — exterior algebra 213-native

## 7. Key Insights (★)

★ **n dimensions = product of n copies of 1 dimension** — Analysis 213
framework lifts directly.

★ **Stokes' theorem = n-dimensional cohomological FTC** — FluxCut +
localDivergence already are the 1D version.

## 8. First Marathon Command

```
"Start Phase MA.  Define MultiCut n + vector arithmetic + unitNCube"
```

