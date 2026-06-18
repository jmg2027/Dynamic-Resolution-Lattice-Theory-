# Euclidean metric identities over the integer lattice

A self-contained package of classical plane-geometry theorems, all stated over the **integer
lattice** `ℤ²` using *squared* distances and the *doubled signed area* — so every quantity stays
in `ℤ`, no `√`, no division, and every identity is either a `ring_intZ` polynomial identity or a
short divisibility argument.  All strict ∅-axiom.

## 213-native answer

There is **no real-number metric primitive** here.  The two readouts are:

- **Squared distance** `sq p q = (p₁−q₁)² + (p₂−q₂)²` — an integer.  The *distance* `√sq` is a
  `Real213` cut (a pointing, never reached); the identities below are all about `sq`, so they live
  entirely in `ℤ`.  Working with `sq` rather than the distance is what makes "classical Euclidean
  geometry" `decide`/`ring`-decidable.
- **Doubled signed area** `area2 A B C = (B₁−A₁)(C₂−A₂) − (B₂−A₂)(C₁−A₁)` — the `2×2` determinant
  `(B−A) × (C−A)`, an integer (the true area is `½·|area2|`, but `area2` itself needs no halving).

Theorems expressible without `√` (squared lengths, signed areas, their det/dot relations) are
ring identities; theorems needing actual distances (Ptolemy, the raw triangle inequality) are the
natural boundary and are **not** in this package — they require the cut layer.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Geometry/` — `StewartTheorem`, `MetricIdentities`, `LatticeArea`
- **∅-axiom status**: **32 PURE / 0 DIRTY**

| file | content | PURE |
|---|---|---|
| `StewartTheorem.lean` | `sq`; Stewart's theorem (`stewart_identity` free form, `stewart_scaled`); median/Apollonius (`apollonius`) | 5 |
| `MetricIdentities.lean` | British flag, parallelogram law, Pythagoras, Leibniz centroid, Euler's quadrilateral | 9 |
| `LatticeArea.lean` | `area2`; shoelace, area additivity, collinearity, symmetry group; Lagrange/Gram, law of cosines, Cayley–Menger; SL₂(ℤ) area invariance | 18 |

## The identities

### Cevians and medians (`StewartTheorem`)
- **Stewart** (free vector form `stewart_identity`): `(m+n)(m·AC² + n·AB²) = |nB+mC−(m+n)A|² + mn·BC²`
  — a pure polynomial identity in the integer coordinates, no triangle hypothesis.  The classical
  `m·AC² + n·AB² = (m+n)(AD² + mn)` follows (`stewart_scaled`) for the cevian foot `D` with
  `(m+n)·D = n·B + m·C`.
- **Apollonius / median** (`apollonius`, `m=n=1`): `2(AB² + AC²) = 4·AD² + BC²`.

### Side–distance identities (`MetricIdentities`)
- **British flag** (rectangle, `u ⊥ v`): `PA² + PC² = PB² + PD²` for any `P`.
- **Parallelogram law**: `AC² + BD² = 2AB² + 2AD²` (free identity).
- **Pythagoras** (right angle at `B`, `u ⊥ v`): `AC² = AB² + BC²`.
- **Leibniz centroid** (`3G = A+B+C`): `PA² + PB² + PC² = GA² + GB² + GC² + 3·PG²` — the
  parallel-axis / `Var(X) = E[X²] − E[X]²` decomposition.
- **Euler quadrilateral**: `AB²+BC²+CD²+DA² = AC²+BD² + 4·MN²` (`M,N` the diagonal midpoints) —
  generalizes the parallelogram law.

In each, a perpendicularity / midpoint / centroid hypothesis collapses a residual cross-term
(`2(u·v)`, `(A+C)−(B+D)`, `A+B+C−3G`) to zero via `eq_of_sub_eq_zero`; the rest is `ring_intZ`.

### Signed area (`LatticeArea`)
- **Shoelace**: `area2 A B C = A₁(B₂−C₂) + B₁(C₂−A₂) + C₁(A₂−B₂)`.
- **Additivity** (barycentric): `[PAB] + [PBC] + [PCA] = [ABC]` for any `P`.
- **Symmetry group**: translation-invariant, cyclic, orientation-flip negates; `Collinear := area2 = 0`.
- **2D Lagrange / Gram**: `area2² = AB²·AC² − ((B−A)·(C−A))²`.
- **Law of cosines**: `BC² = AB² + AC² − 2·((B−A)·(C−A))`.
- **Cayley–Menger / Heron-squared**: `16·Area² = 4·AB²·AC² − (AB²+AC²−BC²)²` — the bridge between
  signed area and squared side lengths.
- **SL₂(ℤ) area invariance**: `area2(MA, MB, MC) = det(M)·area2(A,B,C)`; `det = 1` preserves it —
  the geometric root of the modular group's lattice action.

## Craft notes

- `ring_intZ` treats `^` as opaque (expand to explicit `*`) and times out beyond ~degree-6
  multivariate.  **Cayley–Menger is degree 8** and defeats `ring_intZ` directly; it is closed by
  *decomposing* through the lower-degree 2D-Lagrange (deg 4) + law-of-cosines (deg 2) lemmas plus
  an **abstract assembly step** that holds `AB², AC², BC², dot, area2` as opaque atoms.  Reusable
  lesson: the tactic's degree-ceiling is not a hard wall — factor high-degree identities through
  intermediate named quantities held abstract.
- `ring_intZ` does not cancel `t + (−t)`; collapse zero-factors explicitly (`sub_self_zero` +
  `mul_zeroZ`).  It also does not iota-reduce pair projections `(a,b).1`; feed a `show` with the
  projection pre-applied.
