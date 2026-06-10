# Discrete curvature, parametric across graph families

**Status**: closed ∅-axiom.  Four modules, 129 PURE / 0 DIRTY
(`OllivierRicci` 60, `BakryEmery` 42, `BakryEmeryBipartite` 16,
`DiscreteLichnerowicz` 11).  Companion chapters:
`riemannian_curvature_tensor.md` (the smooth-side algebraic tensor
calculus) and `geometrization_conjecture.md` (the R1 reading this
ladder serves).

## Overview

Curvature, read 213-natively, is not a property of a continuum — it is a
**count-Lens readout of a finite stencil**: what one integer expression
says about how a function's second differences sit against its first
differences at a vertex.  This chapter closes that reading
*parametrically*: not curvature of this or that example graph, but
curvature as a **function of the family parameter** — `K_m` for all `m`,
`K_{1,b}` for all `b`, `K_{a,b}` for all `a, b` — and then the first
consequence of curvature, the spectral gap (Lichnerowicz).  Every
statement is an `Int` identity or inequality over `gridSumZ`
(`Lib/Math/Combinatorics/IntGridSum`); no measure theory, no manifold,
no limit.

## Lean source

- Path: `lean/E213/Lib/Math/Geometry/GeometrizationConjecture/`
- Files: `OllivierRicci.lean` (60 PURE), `BakryEmery.lean` (42 PURE),
  `BakryEmeryBipartite.lean` (16 PURE), `DiscreteLichnerowicz.lean`
  (11 PURE)
- ∅-axiom status: 0 DIRTY — every theorem `#print axioms → "does not
  depend on any axioms"`
- Shared infra: `Lib/Math/Combinatorics/IntGridSum.lean` (the
  `gridSumZ` toolkit, 14 PURE)

## Narrative

### Two faces of one readout

The ladder carries two classical curvature notions, and they are two
Lens readings of the same stencil data:

- **Ollivier–Ricci** reads curvature through *transport*: `κ(x,y) =
  1 − W₁(m_x, m_y)/d(x,y)`, how much cheaper it is to move the
  neighbourhood measure of `x` onto that of `y` than to move the points
  themselves.  Its ∅-axiom heart is `kantorovich_weak_duality` — for any
  transport plan `π ≥ 0` and 1-Lipschitz potential `f`, the dual value
  bounds the primal cost — so a *plan meeting a potential* pins `W₁`
  exactly (`ollivier_bracket`, `ollivier_plan_optimal`).
- **Bakry–Émery** reads curvature through the *carré-du-champ
  iteration*: `Γ₂ = ½LΓ − Γ(f, Lf)`.  A graph satisfies `CD(K, ∞)` when
  `Γ₂ ≥ K·Γ` for every `f` — the synthetic (Lott–Sturm–Villani) meaning
  of "Ricci ≥ K".  Its ∅-axiom heart is a **discrete Bochner identity**
  per family: `Γ₂` expands into `K·Γ` plus an explicit sum of squares.

Both are stencil-parametrised integer identities; the proof idiom
throughout is `ring_intZ` for the Bochner expansion plus
`int_sq_nonneg`/`gridSumZ_nonneg` for the SOS remainder.

### The parametric families

| Family | Bakry–Émery | Ollivier | Lean |
|---|---|---|---|
| line / large cycle | `CD(0, 2)` (flat) | — | `cd_0_2_line` |
| complete `K_m` | `CD((m+2)/2, ∞)` **sharp** | `κ = (m−2)/(m−1) > 0` | `cd_complete_graph{,_sharp}`, §7 `kmPi` chain |
| star `K_{1,b}` centre | `CD((3−b)/2, ∞)` (negative for `b ≥ 4`) | — | `cd_star`, `star_negatively_curved` |
| star `K_{1,b}` leaf | `CD((5−b)/2, ∞)` | — | `cd_star_leaf` |
| bipartite `K_{a,b}`, `A`-vertex | `CD(min(3a−b, b−a+4)/2, ∞)` | — | `kab_cd_wide`, `kab_cd_narrow` |
| triangle / square / double-star | `CD(5/2)` / — / — | `κ = ½` / `0` / `−2/3` | `cd_triangle`, `triangle_*`, `c4_*`, `ds_*` |

The bipartite bound splits at `b = 2a−2`: the **wide** regime closes by
SOS alone (`kab_cd_wide`), the **narrow** regime needs the discrete
Cauchy–Schwarz inequality `cauchy_schwarz_gridZ` — completing the square
over the free second shell (`kab_shell_sos`) is no longer enough, the
cross terms must be traded against the shell mass.  The split is the
arithmetic of the stencil, not a proof artifact: at `b = 2a−2` the two
expressions for the curvature coincide.

### The DRLT core and an honest cross-frame divergence

The central lattice `K_{3,2}` sits in the narrow regime and comes out
**positively** curved: `CD(3/2, ∞)` (`kab_K32_pos`).  Forman curvature
gives the same graph `−1`.  The two frames *disagree in sign* — and
that is a finding, not an error: Forman reads edge-neighbourhood
combinatorics, Bakry–Émery reads function-space contraction, and the
claim "all curvature frames agree in sign" is false as stated.  The
corrected synthesis lives in
`theory/essays/synthesis/curvature_as_lens_readout.md`: a curvature is
a *Lens readout*, and distinct Lenses on one object need not order it
the same way.  What the frames do share is the parametric *shape* —
each is an explicit integer function of the family parameters.

### Curvature → spectrum (Lichnerowicz)

`DiscreteLichnerowicz` closes the first classical *consequence* of a
curvature lower bound.  The integration-by-parts trio is explicit:
`km_lap_sq_sum`, `km_f_lap_sum`, `km_dirichlet_sum` combine into
`km_green` and the Rayleigh identity `km_rayleigh` (`Σ(Lf)² = m·E(f)`
on `K_m`).  From it: every non-constant eigenvalue of the `K_m`
Laplacian is `m`, and the eigenspaces are realized exactly —
`km_const_eigen` (constants, eigenvalue `0`) and `km_meanzero_eigen`
(mean-zero functions, eigenvalue `m`) — so the spectrum is
`{0¹, m^{m−1}}`.  The abstract mechanism `lichnerowicz_abstract`
(`CD(K)` ⟹ `K ≤ λ` for any positive eigenvalue, by Int positive
cancellation `OrderMul.le_of_mul_le_mul_right_pos`) ties the two
chapters together: the curvature bound of the previous section *is* a
spectral-gap bound.

## Key results

| Theorem | Module | Statement (informal) |
|---|---|---|
| `kantorovich_weak_duality` | OllivierRicci | dual value ≤ transport cost, all plans × all 1-Lipschitz potentials |
| `ollivier_plan_optimal` | OllivierRicci | a plan meeting a 1-Lipschitz dual is cost-optimal |
| `kmPi` §7 chain | OllivierRicci | `K_m`: Ollivier `κ = (m−2)/(m−1)`, all `m` |
| `cd_complete_graph_sharp` | BakryEmery | `K_m` is `CD((m+2)/2, ∞)` and the constant is optimal |
| `cd_star` / `cd_star_leaf` | BakryEmery | `K_{1,b}`: centre `(3−b)/2`, leaf `(5−b)/2` |
| `kab_cd_wide` / `kab_cd_narrow` | BakryEmeryBipartite | `K_{a,b}` `A`-vertex: `min(3a−b, b−a+4)/2`, both regimes |
| `kab_K32_pos` | BakryEmeryBipartite | DRLT core `K_{3,2}` is `CD(3/2, ∞)` |
| `cauchy_schwarz_gridZ` | BakryEmeryBipartite | discrete Cauchy–Schwarz over `gridSumZ` |
| `km_rayleigh` / `km_eigenvalue` | DiscreteLichnerowicz | `K_m` spectrum `{0¹, m^{m−1}}`, eigenspaces realized |
| `lichnerowicz_abstract` | DiscreteLichnerowicz | `CD(K)` ⟹ `K ≤ λ` |

## Research-note provenance

The A6 Ricci-core ladder and smooth-core attack notes under
`research-notes/frontiers/` (Ricci topic group), and the
curvature↔spectrum cross-domain note there; the closed discrete rungs
1–7 are catalogued in `STRICT_ZERO_AXIOM.md` (A6 CORE entries).

## Open frontier

What is **not** closed here is the smooth analytic core — weighted
integration-by-parts connecting `∇𝓕` to `∂_t g = −2Ric`, the `𝓦`
Gaussian, Li–Yau Harnack, κ-solution/surgery — tracked under
`research-notes/frontiers/` (Ricci-flow smooth core + the
`a6_ricci_core/` ladder), and the cross-domain bridges (additive
characters of `ℤ/p` as the `K_p` eigenbasis vs the multiplicative
Legendre character) tracked in the curvature–spectrum cross-domain
note there.

## How to verify

```bash
cd lean && lake build
python3 tools/scan_axioms.py E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci
python3 tools/scan_axioms.py E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmery
python3 tools/scan_axioms.py E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmeryBipartite
python3 tools/scan_axioms.py E213.Lib.Math.Geometry.GeometrizationConjecture.DiscreteLichnerowicz
```
