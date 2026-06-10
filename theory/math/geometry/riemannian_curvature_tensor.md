# The Riemannian curvature tensor (213-native, dimension-free)

**Status**: the *algebraic* Riemannian curvature tensor calculus is closed
∅-axiom (`lean/E213/Lib/Math/Geometry/TensorCalculus.lean`, 23 PURE / 0 DIRTY;
`ConformalCurvature.lean` §S6–§S7, the conformal route).  The *analytic* core
(transcendental metrics + PDE a-priori estimates behind Perelman's
`𝓦`-monotonicity) is the open frontier, tracked in
`research-notes/frontiers/ricci_flow_smooth_core.md`.

## Overview

Classical Riemannian geometry builds curvature from a smooth metric tensor
field `g`, its Levi-Civita connection, and the non-commutativity of covariant
derivatives — packaged as the Riemann tensor `R^l_{ijk}`, contracted to Ricci
`Ric_{ij}` and scalar `R`.  The smooth manifold, the limit-of-triangles, the
tensor-field analysis are scaffolding.  The 213 reading strips them: curvature
is what a **count-Lens reads off the metric's derivative data**, an integer
index expression, dimension-free — the indices `i,j,k,…` are arbitrary `Nat`
and the metric enters *only* through its derivative tensor.

```
"metric"            = a symmetric derivative tensor  dg a b c = ∂_a g_{bc}
"connection"        = the symmetric combination (Christoffel), no manifold
"curvature"         = the obstruction to that connection being flat
"the index sums"    = gridSumZ contractions over ℤ
```

The whole calculus is `ring_intZ` + `gridSumZ` linearity — *counting*, not
analysis.  What is genuinely analytic (transcendental metrics, PDE estimates)
is isolated as the residual wall, not smuggled in.

## The connection (Christoffel symbols)

The metric enters as `dg a b c = ∂_a g_{bc}`, an abstract `Int`-valued tensor
symmetric in its last two slots (because `g` is symmetric).  No smooth metric,
no chart — just the derivative data.

**First kind** (`chris1x2`, scaled `×2` to stay over ℤ):

```
2·Γ_{kij} = ∂_i g_{kj} + ∂_j g_{ki} − ∂_k g_{ij}
```

needs **no metric inverse**, hence no division — pure polynomial counting.  Its
two defining identities are the Levi-Civita axioms:

- **torsion-free** `Γ_{kij} = Γ_{kji}` (`chris1_symm`, from `g`-symmetry);
- **metric compatibility** `Γ_{kij} + Γ_{jik} = ∂_i g_{kj}` (`chris1_metric_compat`)
  — the identity `∇g = 0` that *defines* the connection as "metric".

**Second kind** raises the lower index with the inverse metric.  Over ℤ the
inverse `g^{lm} = adj^{lm}/det g` carries a `det` denominator, so we work with
the `det`-scaled `2·det·Γ^l_{ij} = Σ_m adj^{lm}·2Γ_{mij}` (`chris2xDet`,
`gridSumZ` over `m`), the adjugate abstract via `g·adj = det·I` (`hadj`).  The
content is the raising/lowering consistency `chris2_lower`:

```
Σ_l g_{pl}·(2·det·Γ^l_{ij}) = det·2Γ_{pij}
```

— "`Γ^l` is `Γ_l` with the index raised by `g^{-1}`", proven via `gridSumZ`
Fubini + the Kronecker collapse `gridSumZ_delta_weight`.

## The Riemann tensor and its symmetries

From the connection `Gam l i j = Γ^l_{ij}` and its derivative
`dGamma a l i k = ∂_a Γ^l_{ik}` (abstract, as the metric entered via `dg`):

```
R^l_{ijk} = ∂_j Γ^l_{ik} − ∂_k Γ^l_{ij} + Σ_m(Γ^l_{jm}Γ^m_{ik} − Γ^l_{km}Γ^m_{ij})
```

(`riemUp`).  Defining facts: `riem_antisym_jk` (`R^l_{ijk} = −R^l_{ikj}`, the
curvature `2`-form / `[∇_j,∇_k]` commutator) and `riem_flat` (a flat connection
has `R ≡ 0` — no curvature).

The deeper **algebraic symmetries** are pointwise; in normal coordinates
(`Γ = 0` at a point, the `ΓΓ` terms drop) the lowered Riemann is the metric
**2-jet**:

```
2·R_{iklj} = ∂_i∂_j g_{kl} + ∂_k∂_l g_{ij} − ∂_i∂_l g_{kj} − ∂_k∂_j g_{il}
```

(`riemLow`, from `ddg a b c d = ∂_a∂_b g_{cd}`, symmetric in `(a,b)` since `∂∂`
commute and in `(c,d)` since `g` is symmetric).  All **four** curvature
symmetries follow from those two 2-jet symmetries, dimension-free:

| symmetry | theorem | from |
|---|---|---|
| `R_{iklj} = −R_{kilj}` | `riemLow_antisym_ik` | pure `ring` |
| `R_{iklj} = −R_{ikjl}` | `riemLow_antisym_lj` | pure `ring` |
| `R_{iklj} = R_{ljik}` (block) | `riemLow_pair_symm` | `hd`/`hg` |
| `R_{iklj} + R_{iljk} = −R_{ijkl}` (Bianchi) | `riemLow_bianchi1` | `hd`/`hg` |

The first Bianchi is stated in *moved-over* form (non-zero both sides) to
sidestep `ring_intZ`'s zero-polynomial gap; the abstract `riemUp` version
(`riem_bianchi1`, torsion-free `Γ`) combines the six `ΓΓ` contractions into one
`gridSumZ` whose summand cancels per-`m`.

## Ricci, scalar, and the Einstein condition

**Ricci** is the trace `Ric_{ik} = Σ_l R^l_{ilk}` (`ricciFromRiem`); flat ⟹
Ricci-flat (`ricci_flat`, the Einstein vacuum).  **Scalar** is the metric trace
`det·R = Σ_{i,j} adj^{ij}·Ric_{ij}` (`scalarFromRicci`).  Its content is the
**Einstein** relation `scalar_einstein`:

```
Ric_{ij} = λ·g_{ij}  ⟹  R = λ·n
```

— constant scalar = Einstein constant × dimension (since `tr(adj·g) = n·det`).
Einstein metrics are the Ricci-flow fixed points; this is their defining scalar.

The **conformal route** reaches curvature for the conformally-flat class
`g = λ·δ` in general `n` without the inverse machinery
(`ConformalCurvature.lean`): the scalar `R = −(n−1)(4λΔλ+(n−6)|∇λ|²)/(4λ³)`
(`confRNumN`, validated `= 4·confKNum` at `n=2`, the Liouville case) and the
conformally-flat Ricci tensor (`confRic*`), with the 3D (Poincaré-dimension)
flat/positive/negative trichotomy on polynomial `λ`.

## Perelman's monotonicity rate, as a sum of squares

Because `Ric` and the Hessian `Hess f = ∂_i∂_j f` (the same 2-jet pattern) are
now ∅-axiom objects, the *reason Perelman's entropy `𝓕` is monotone* becomes a
finite algebraic fact.  Perelman's identity is

```
d/dt 𝓕 = 2 ∫ |Ric_{ij} + ∇_i∇_j f|² e^{−f} dV ≥ 0,
```

the rate a **sum of squares** of the symmetric tensor `Ric + Hess f`.  With the
integral a finite `gridSumZ` contraction and the positive weight `e^{−f}dV ≡ 1`:

```
0 ≤ Σ_{i,j} (Ric_{ij} + ∇_i∇_j f)²
```

(`perelman_rate_nonneg`) — the monovariant's non-negative descent rate,
curvature term included, no new primitive (the `BakryEmery` SOS idiom
`gridSumZ_nonneg ∘ int_sq_nonneg`).

## Open frontier

The *algebraic* tensor calculus is closed; the residual wall is pure
**analysis**, tracked in `research-notes/frontiers/ricci_flow_smooth_core.md`:
the weighted integration-by-parts that *connects* `∇𝓕` to the flow
`∂_t g = −2Ric` (so "Ricci flow IS the gradient flow of `𝓕`" stays a premise),
the `(4πτ)^{−n/2}e^{−f}` Gaussian of the true `𝓦`-entropy (the transcendental
tier — itself a `Real213` packaging task, not a conceptual wall), the nonlinear
Li–Yau / differential Harnack, and the κ-solution / surgery classification +
no-local-collapsing compactness — the genuine century-problem core.
