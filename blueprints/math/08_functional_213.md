# Functional Analysis 213 — Blueprint

**Priority**: ★ (undergraduate 3-4 year math, quantum mechanics applications)

---

## 1. Why This Field

ZFC functional analysis:
- Banach space (norm), Hilbert space (inner product)
- Operator theory, spectral theorem
- Hahn-Banach, open mapping (Choice-dependent!)

Natural emergence in 213:
- **Analysis 213**'s Cut space is a natural functional space
- **CayleyDickson**'s ℤ[i] etc. are inner product space candidates
- Just as σ-algebra was rejected, **non-constructive theorems rejected**

## 2. 213-native Emergence

### 2.1 Cut space = function space

`Cut → Cut` itself is a function space.  norm, inner product definable:

```
def cutNorm (f : Cut → Cut) : Cut := ...   -- sup over dyadic
def cutInner (f g : Cut → Cut) : Cut := ∫ f * g dx
```

### 2.2 Banach space — Cauchy complete

Analysis 213's `CauchyCutSeq` already provides Cauchy completeness.  Banach
space = Cauchy completeness of functions.

### 2.3 Hilbert space

Inner product = `cutInner`.  `IsAntiderivative.integral` directly
utilized.  L² space natural.

### 2.4 Operator + spectrum

Linear operator T : Cut → Cut.  Spectrum = `cohomEquiv` form
eigenvalue.

### 2.5 Hahn-Banach rejected

ZFC's Hahn-Banach depends on Choice.  In 213: **directly
constructible extension** only.  This is a *feature*, not a *restriction*.

## 3. Building Blocks

- Analysis 213 (cut, IsDifferentiable, Cauchy)
- Measure 213 (Lebesgue 213)
- Complex 213 (complex Hilbert)

## 4. Phase Plan

### Phase FA — Norm + Cauchy (3-5 commits)

1. Define `cutNorm` + propEq sup
2. Cauchy completeness (using Analysis 213)
3. Banach skeleton

### Phase FB — Inner product + Hilbert

1. `cutInner` via integral
2. Cauchy-Schwarz propEq
3. Orthogonal projection

### Phase FC — Operator + spectrum

1. Linear operator on Cut → Cut
2. Bounded operator
3. Spectrum (eigenvalue) — starting from finite dim

### Phase FD — Capstone

First year undergraduate functional analysis.

## 5. Connections to Other Tracks

- **Atoms**: orbital = element of Hilbert space
- **Quantum gravity**: amplitude
- **Yang-Mills**: gauge field space
- **DHA**: Fourier basis = orthonormal

## 6. Open Problems

- **Hahn-Banach** — no Choice → constructive part only
- **Open mapping theorem** — likewise
- **Spectral theorem general** — partial only

## 7. Key Insights (★)

★ **Banach completion = Cauchy** — Analysis 213 directly applicable.

★ **L² = cutPow integrable** — Measure 213 + Analysis 213 combined.

★ **Choice rejected = constraint vs feature** — tests feasibility of formal
quantum mechanics with constructive methods only.

## 8. First Marathon Command

```
"Start Phase FA.  cutNorm + Banach skeleton on Cut → Cut"
```

