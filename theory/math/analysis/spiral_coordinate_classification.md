# Spiral-coordinate classification of reals — two orthogonal counts and a residue

**Status**: Closed.  Source of truth (all ∅-axiom):
`lean/E213/Lib/Math/Real213/{SpiralLayer, SpiralCoordinate}`,
`lean/E213/Lib/Math/CayleyDickson/Integer/{ZIUnits, GaussianCrossDet, EisensteinCrossDet,
EisensteinCompletion, ZOmegaUnits}`,
`lean/E213/Lib/Math/Cauchy/{DivergenceLadder, DivergenceDepth, DepthPiQuartic,
DepthCoordGenerator}`.

## Overview

A classification of the reals finer than algebraic / transcendental, and orthogonal to the
Mahler–Koksma–irrationality-measure hierarchy.  A real — more precisely a *holonomic
presentation* of one, the coordinates are intensional — sits at a point with **two
independent 213-native count-coordinates** plus a residue:

  - **layer** = the divergence depth (how many cross-determinant → ratio → finite-difference
    lifts reach a constant floor), a count in `ℕ ∪ {∞}`;
  - **axis** = the order of the unit group of the ring carrying the cut's approximation
    (`ℤ`, `ℤ[i]`, `ℤ[ω]`), a count in **exactly** `{2, 4, 6}`.

The **spiral** itself — the continued-fraction expansion engine (`x ↦ 1/(x − ⌊x⌋)`, the
det-one floor universal to every real) — is the non-classifying substrate the two
coordinates index.  The **residue** is layer `∞` (rate-free / non-holonomic presentations)
together with the top-less depth tower.

## Lean source

| File | PURE / dirty | Content |
|---|---|---|
| `Real213/SpiralLayer.lean` | 2 / 0 | the layer is intensional (`depth_is_intensional`); spectrum is all of `ℕ` (`depth_spectrum_unrestricted`) |
| `Real213/SpiralCoordinate.lean` | 1 / 0 | `spiral_coordinate`: the two orthogonal counts bundled |
| `CayleyDickson/Integer/ZIUnits.lean` | 6 / 0 | the Gaussian 4-theorem (`ZI_units_exact_four`, `\|ℤ[i]^×\| = 4`) |
| `CayleyDickson/Integer/GaussianCrossDet.lean` | 11 / 0 | the `ℤ[i]` floor rotates with order 4 (`gaussian_floor_rotation`, `μ = −i`) |
| `CayleyDickson/Integer/EisensteinCrossDet.lean` | 14 / 0 | the `ℤ[ω]` cross-det rides the 6-unit floor (`crossDet_on_units`) |
| `CayleyDickson/Integer/EisensteinCompletion.lean` | 9 / 0 | the `ℤ[ω]` floor rotates with order 6 (`eisenstein_floor_rotation`); completion factors through the real norm |
| `Cauchy/DivergenceDepth.lean`, `DepthPiQuartic.lean` | — | e depth 3, π ratio depth 4 (depth 6) |
| `Cauchy/DepthCoordGenerator.lean` | — | every finite depth realized exactly (`genExp_depth_exact`) |

Builds under the `E213.Lib.Math.Real213` and `E213.Lib.Math.CayleyDickson` umbrellas.

## Narrative

### The layer — divergence depth, intensional

The cross-determinant of a real's convergents, lifted by ratio then finite differences,
reaches a constant floor in a finite number of steps (or never).  That number is the
**divergence depth**.  An algebraic irrational (φ, √2) has depth 1 — its cross-determinant
is *already* constant (`±1`, the Cassini / Pell unit).  e has depth 3 (cross-determinant
`n!`, ratio `n+1`, one difference to the constant `1`).  π has depth 6 (its Wallis-product
ratio is a degree-4 polynomial, four differences to a constant — `piRatio_polyDepth`).
Liouville has depth `∞` (super-polynomial growth, never floors).

Two facts pin this coordinate honestly.

  - **It is intensional.**  In the *regular* continued fraction the cross-determinant is on
    the `±1` floor for **every** real (`cf_det_sq`, `W² = 1` for any partial-quotient
    sequence) — the regular CF collapses every real to depth 1.  The depths 3 and 6 live in
    the *series* presentations (e: factorial; π: Wallis).  So the layer classifies the
    holonomic presentation, not the bare real; the cut is the gauge-invariant
    (`depth_is_intensional`, matching `Real213/IntensionalCompletability`).
  - **Its spectrum is all of `ℕ`.**  Every finite depth `d` is realized *exactly* by the
    binomial-column generator `genExp d` (`depth_spectrum_unrestricted`,
    `genExp_depth_exact`).  The values `{1, 3, 6}` of `{φ, e, π}` are a selection — the
    ratio-degrees `{0, 1, 4}` — not a privileged (e.g. triangular) subset; depths `2, 4, 5`
    are occupied by other constants.

The layer is **orthogonal to the Mahler–Koksma–μ hierarchy**: that hierarchy places e and π
in the same class (both `S`, both `μ = 2`) and cannot separate them.  The depth (e `3` < π
`6`) tracks instead the *continued-fraction holonomicity* — patterned CF (e) versus
irregular CF (π) — the one classical axis that distinguishes them.  "Rate-carrying versus
rate-free" is "holonomic CF versus non-holonomic CF".

### The axis — arithmetic unit-group order, exactly `{2, 4, 6}`

The convergent cross-determinant is always a unit of the coefficient ring (the Cassini
identity gives `(−1)ⁿ`).  The *order* of that unit group is the axis coordinate.  By
Dirichlet's unit theorem an imaginary-quadratic ring has free rank 0, so its units are
exactly the roots of unity; and `φ(m) ≤ 2` forces `m ∈ {1,2,3,4,6}`, i.e. orders
**`{2, 4, 6}`** — with 4 and 6 pinned to `ℤ[i]` and `ℤ[ω]`.  This is a complete finite
classification.  Both extra orders are built here as exact-cardinality theorems mirroring
each other: the Gaussian 4-theorem (`ZI_units_exact_four`) and the Eisenstein 6-theorem
(`ZOmega_units_exact_six`, with `6 = NS·NT`).

The axis is realized *geometrically* as a floor rotation.  With a unit-coefficient
recurrence `s_{n+2} = s_{n+1} + q·s_n`, the cross-determinant is multiplied each step by
`−q`; when `q` is a primitive unit the cross-determinant walks the whole unit group:

  | axis | ring | rotation multiplier | period |
  |---|---|---|---|
  | 2 | `ℤ` | `−1` | 2 (`W = ±1`, `cf_det_sq`) |
  | 4 | `ℤ[i]` | `−i` | 4 (`gaussian_floor_rotation`) |
  | 6 | `ℤ[ω]` | `−ω` | 6 `= NS·NT` (`eisenstein_floor_rotation`) |

This rotation is a specific algebraic recurrence, distinct from the canonical Hurwitz
nearest-integer continued fraction (whose cross-determinant is `(−1)ⁿ ∈ {±1}` in every
ring); the full unit group enters precisely through the primitive-unit coefficient.

The three axes carry a transcendental shadow through the Chowla–Selberg / Gross CM-period
formula (the unit order `w` appears in its exponent): `Γ(1/2) ∼ π` at the boundary, `Γ(1/4)`
at disc `−4` (`ℤ[i]`), `Γ(1/3)` at disc `−3` (`ℤ[ω]`).  This is interpretive, not
formalised; the single-`Γ` collapse is exact only for these small-discriminant cases.

### The two coordinates are independent

The layer projection is surjective onto `ℕ` at the fixed real axis (`ℤ`, order 2) — every
depth is realized by an explicit `ℤ`-sequence (`genExp`).  The axis projection is surjective
onto `{2, 4, 6}` at the fixed minimal layer (the det-one / unit floor) — `ℤ`, `ℤ[i]`, `ℤ[ω]`
all carry a unit-floor cross-determinant.  Neither coordinate constrains the other:
`spiral_coordinate` bundles the two surjectivities, and `depth_is_intensional` shows the
layer is free of the bare real.  Their ranges differ in kind — the layer is an unbounded
count in `ℕ`, the axis a finite count in `{2, 4, 6}`.

### The completion asymmetry

Convergence is a property of the **real** axis.  Over `ℤ` every partial-quotient sequence
`a_i ≥ 1` completes unconditionally (`cf_universal_total_modulus`).  Over the complex axes
it is conditional — the Hurwitz nearest-integer algorithm needs a minimum-modulus condition
(`|a_n| ≥ √2`) and forbidden-block admissibility, and the convergent gaps shrink only when
the denominator *norms* grow.  Those norms are a `ℤ`-quantity: the gap scale factors as
`‖q_n q_{n+1}‖² = ‖q_n‖²·‖q_{n+1}‖²` (`gap_scale_factors`), so Eisenstein convergence
factors through the real growth of the norm form, and the real slice (`ℤ ⊂ ℤ[ω]`, norms are
perfect squares) embeds as the completing diagonal (`eisenstein_real_slice_completes`).  The
2-axis is the only unconditionally-completing one; the higher axes add rotation, not a new
convergence mechanism.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `depth_is_intensional` | `SpiralLayer` | regular CF ⇒ depth-1 floor universal; e `3`, π `6` are series-presentation depths |
| `depth_spectrum_unrestricted` | `SpiralLayer` | every finite depth realized exactly; `{1,3,6}` is a selection, not a law |
| `ZI_units_exact_four` | `ZIUnits` | `\|ℤ[i]^×\| = 4` (the Gaussian 4-theorem) |
| `gaussian_floor_rotation` | `GaussianCrossDet` | the `ℤ[i]` floor rotates by `−i`, order 4 |
| `eisenstein_floor_rotation` | `EisensteinCompletion` | the `ℤ[ω]` floor rotates by `−ω`, order `6 = NS·NT` |
| `spiral_coordinate` | `SpiralCoordinate` | the two orthogonal counts (layer intensional + unrestricted; axis `{2,4,6}`) |

## Open frontier

The single open input is the **non-holonomicity of π's continued fraction** — whether π's
partial quotients satisfy no linear recurrence with polynomial coefficients.  This is a
classical open problem, not closable ∅-axiom here; it is what would turn "π is rate-free"
from an observation into a theorem.  The provable direction — a holonomic / P-recursive
presentation has finite divergence depth — is already closed (`Cauchy/DepthPRecursive`).
The CM-period shadow (`Γ(1/3)`, `Γ(1/4)`) is interpretive: periods are not ∅-axiom integer
data, so the chapter pins the algebraic skeleton (unit orders, rotations) the periods hang
on, not the periods themselves.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Real213 E213.Lib.Math.CayleyDickson
cd ..
for M in \
  E213.Lib.Math.Real213.SpiralLayer \
  E213.Lib.Math.Real213.SpiralCoordinate \
  E213.Lib.Math.CayleyDickson.Integer.ZIUnits \
  E213.Lib.Math.CayleyDickson.Integer.GaussianCrossDet \
  E213.Lib.Math.CayleyDickson.Integer.EisensteinCompletion ; do
    python3 tools/scan_axioms.py $M
done
```
Each module reports `N pure / 0 dirty`.
