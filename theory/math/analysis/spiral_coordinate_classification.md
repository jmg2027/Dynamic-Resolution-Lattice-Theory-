# Spiral-coordinate classification of reals — two orthogonal counts and a residue

**Status**: Closed.  Source of truth (all ∅-axiom):
`lean/E213/Lib/Math/NumberSystems/Real213/{SpiralLayer, SpiralCoordinate}`,
`lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/{ZIUnits, GaussianCrossDet, EisensteinCrossDet,
EisensteinCompletion, ZOmegaUnits}`,
`lean/E213/Lib/Math/Analysis/Cauchy/{DivergenceLadder, DivergenceDepth, DepthPiQuartic,
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
| `Real213/Spiral/SpiralLayer.lean` | 2 / 0 | the layer is intensional (`depth_is_intensional`); spectrum is all of `ℕ` (`depth_spectrum_unrestricted`) |
| `Real213/Spiral/SpiralCoordinate.lean` | 1 / 0 | `spiral_coordinate`: the two orthogonal counts bundled |
| `CayleyDickson/Integer/ZIUnits.lean` | 6 / 0 | the Gaussian 4-theorem (`ZI_units_exact_four`, `\|ℤ[i]^×\| = 4`) |
| `CayleyDickson/Integer/ImaginaryQuadraticUnitTrichotomy.lean` | 7 / 0 | the axis is exhaustively `{2,4,6}` (`unitForm_generic_axis`: `d ≥ 2 ⇒` only `±1`; `imaginary_quadratic_unit_trichotomy`; `maximal_order_no_complex_unit`; `axis_binary_cover`) |
| `CayleyDickson/Tower/SpiralAxisCrystallographic.lean` | 1 / 0 | verified bridge: `{2,4,6}` = even half of crystallographic `{1,2,3,4,6}` = `2·{1,2,3}` |
| `CayleyDickson/Integer/GaussianCrossDet.lean` | 11 / 0 | the `ℤ[i]` floor rotates with order 4 (`gaussian_floor_rotation`, `μ = −i`) |
| `CayleyDickson/Integer/EisensteinCrossDet.lean` | 14 / 0 | the `ℤ[ω]` cross-det rides the 6-unit floor (`crossDet_on_units`) |
| `CayleyDickson/Integer/EisensteinCompletion.lean` | 9 / 0 | the `ℤ[ω]` floor rotates with order 6 (`eisenstein_floor_rotation`); completion factors through the real norm |
| `Cauchy/DivergenceDepth.lean`, `DepthPiQuartic.lean` | — | e depth 3, π ratio depth 4 (depth 6) |
| `Cauchy/DepthCoordGenerator.lean` | — | every finite depth realized exactly (`genExp_depth_exact`) |

Builds under the `E213.Lib.Math.NumberSystems.Real213` and `E213.Lib.Math.Algebra.CayleyDickson` umbrellas.

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

The **exhaustiveness** — that no fourth axis occurs — is closed `∅`-axiom in
`ImaginaryQuadraticUnitTrichotomy`.  For the recurrence coefficient ring `ℤ[√−d]` a unit
is a solution of the norm form `a² + d·b² = 1`, and `unitForm_generic_axis` proves that
for **every** `d ≥ 2` the only solutions are `(±1, 0)`: a non-zero `b` already gives
`d·b² ≥ d ≥ 2 > 1`.  So every axis past the Gaussian one collapses to the bare `{±1}`
(order 2); `imaginary_quadratic_unit_trichotomy` bundles this with the order-4 (`ℤ[i]`)
and order-6 (`ℤ[ω]`) points.  The axis coordinate has a **closed finite range**, not three
sampled instances — the classical Dirichlet trichotomy made constructive (the proof runs
through `Int.natAbs` into `Nat`, no `ring`, no `omega`).

The `ℤ[√−d]` recurrence family does not exhaust the imaginary-quadratic *maximal* orders:
for `d ≡ 3 (mod 4)` the maximal order is the denser `ℤ[(1+√−d)/2]`, norm `a² + a·b + c·b²`
with `c = (1+d)/4`.  `maximal_order_no_complex_unit` closes this last case too: scaling the
norm by `4` gives `(2a+b)² + d·b² = 4` (since `4c − 1 = d`), and for `d ≥ 5` the same
kernel (`nat_form_forces_b_zero` at `N = 4`) forces the imaginary part `b = 0` — every unit
is real, so the order is `ℤ^× = {±1}`.  Eisenstein (`d = 3`) is the unique reduced-form
order with a complex unit, so the trichotomy holds for **all** imaginary-quadratic maximal
orders, not just the `ℤ[√−d]` family.

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

### The axis is the binary cover — `{2,4,6} = 2·{1,2,3}`

The three axis orders are not three unrelated numbers: `{2,4,6} = 2·{1,2,3}` is the **even
half** of the crystallographic restriction `{1,2,3,4,6}` (`φ(m) ≤ 2`,
`Tower/CyclotomicTraceDegree.crystallographic_restriction`), and the doubling factor is
structural.  Each floor-rotation multiplier `μ` reaches the central unit `−1` at its
*midpoint* power `k ∈ {1,2,3}` and the identity at `2k ∈ {2,4,6}` (`axis_binary_cover`):

  | axis | `μ` | midpoint `μᵏ = −1` | full `μ²ᵏ = 1` |
  |---|---|---|---|
  | 2 | `−1` | `μ¹ = −1` (`k=1`) | `μ² = 1` |
  | 4 | `−i` | `μ² = −1` (`k=2`) | `μ⁴ = 1` |
  | 6 | `ζ₆` | `μ³ = −1` (`k=3`, `zeta6_cubed`) | `μ⁶ = 1` (`zeta6_pow_six`) |

The factor `2` is the central involution `−1` — the **Cassini sign** `(−1)ⁿ` carried by
every cross-determinant.  This central `−1` is the `2`-fold cover: the spiral floor sits one
central `−1` above the bare point-rotation `{1,2,3}`.  It is the structural origin of the
word *binary* in the binary-polyhedral rungs `E₆ = 2T, E₇ = 2O, E₈ = 2I`
(`Tower/BinaryPolyhedralTower`, `Tower/MckayADECensus`): the spiral axis, read dynamically
off a continued-fraction cross-determinant, is the same `2`-fold cover that makes the
exceptional groups *binary*.

This identification is itself a checked fact, not only a reading.
`Tower/SpiralAxisCrystallographic.spiral_axis_is_even_crystallographic` bundles three
decidable identities: the crystallographic orders are `{1,2,3,4,6}`
(`crystallographic_restriction`, the `GL(2,ℤ)` census `φ(m) ≤ 2`), their even members are
exactly the spiral axis `{2,4,6}`, and `{2,4,6} = 2·{1,2,3}`.  So the arithmetic unit-group
axis (read off a continued fraction) and the geometric rotation census (read off `GL(2,ℤ)`)
are the same `{1,2,3}` seen through one binary cover — the analysis side and the
exceptional-tower side meet on `{1,2,3}`.

What the axis is *not*: the **Cayley–Dickson dimension tower** `{1,2,4,8} = 2ⁿ`.  The tempting
`1,2,4,8 ↔ {2,4,6}` map is a stereotype — the two sequences meet only on `{2,4}` and then diverge
for two independent reasons (`Tower/SpiralAxisCrystallographic.cd_tower_axis_noncoincidence`): the
octonion dimension `8 = 2³` is a power of two but **not** a crystallographic order (`φ 8 = 4 > 2`;
since the axis is the even half of the crystallographic set, `8` is off it — *no octonion at the
axis*), while the axis order `6` is crystallographic (`φ 6 = 2`) but **not** a power of two
(`not_pow_two_six` — *no order-6 Cayley–Dickson rung*).  The Cayley–Dickson content of the axis runs
through the *rings* `ℤ[i], ℤ[ω]` (unit orders `4, 6`), not the dimension doubling `2ⁿ`.

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
| `unitForm_generic_axis` | `ImaginaryQuadraticUnitTrichotomy` | `d ≥ 2 ⇒ a²+d·b²=1` only at `(±1,0)`: no fourth axis |
| `imaginary_quadratic_unit_trichotomy` | `ImaginaryQuadraticUnitTrichotomy` | the axis is exactly `{2,4,6}`, a closed finite range |
| `maximal_order_no_complex_unit` | `ImaginaryQuadraticUnitTrichotomy` | `d ≡ 3 (mod 4)` maximal orders (`d≥5`): `(2a+b)²+d·b²=4 ⇒ b=0`, no complex unit |
| `axis_binary_cover` | `ImaginaryQuadraticUnitTrichotomy` | `{2,4,6}=2·{1,2,3}`: midpoint `μᵏ=−1`, the central `−1` is the binary cover |
| `spiral_axis_is_even_crystallographic` | `Tower/SpiralAxisCrystallographic` | `{2,4,6}` = even half of crystallographic `{1,2,3,4,6}` = `2·{1,2,3}` (verified bridge) |
| `gaussian_floor_rotation` | `GaussianCrossDet` | the `ℤ[i]` floor rotates by `−i`, order 4 |
| `eisenstein_floor_rotation` | `EisensteinCompletion` | the `ℤ[ω]` floor rotates by `−ω`, order `6 = NS·NT` |
| `spiral_coordinate` | `SpiralCoordinate` | the two orthogonal counts (layer intensional + unrestricted; axis `{2,4,6}`) |

## Open frontier

The single open input is the **non-holonomicity of π's continued fraction** — whether π's
partial quotients satisfy no linear recurrence with polynomial coefficients.  This is a
classical open problem, not closable ∅-axiom here; it is what would turn "π is rate-free"
from an observation into a theorem.  The provable direction — a holonomic / P-recursive
presentation has finite divergence depth — is already closed (`Cauchy/DepthPRecursive`).

This frontier has a **third spiral-layer reading** — the divergence-depth of the
*partial-quotient sequence* `(aᵢ)` itself (distinct from the convergent cross-determinant,
which is the det-one floor for every real).  Its provable neighbours are closed in
`Cauchy/HurwitzianCF`: the quasi-polynomial class `QuasiPolyCF p a` (partial quotients
polynomial on each residue class mod `p`, the formal handle on "Hurwitzian / holonomic
partial quotients"), with the tiers **0** periodic-CF ⟹ quasi-polynomial
(`periodic_quasipoly`, quadratic irrationals) and **1** e's `[2;1,2k,1]` pattern is
`QuasiPolyCF 3` (`e_cf_quasipoly` — the folklore "Hurwitzian ⟹ holonomic" made an explicit
∅-axiom theorem), plus the certificate `polyDepth d ⟹ Δ^{d+1} = 0` (constant-coefficient
recurrence, C-finite per section).  π is the conjectured **tier ∞**; the CF-holonomicity
tier is conjectured to separate e from π where the irrationality measure does not (both
`μ = 2`, conditionally for π).  The credible route to non-holonomicity is the
Flajolet–Gerhold–Salvy asymptotic obstruction (holonomic sequences have asymptotics of the
restricted form `C·ρ⁻ⁿ·n^θ·(log n)^κ`), against which π's Gauss–Kuzmin partial-quotient
statistics are conjecturally incompatible.
The CM-period shadow (`Γ(1/3)`, `Γ(1/4)`) is interpretive: periods are not ∅-axiom integer
data, so the chapter pins the algebraic skeleton (unit orders, rotations) the periods hang
on, not the periods themselves.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.NumberSystems.Real213 E213.Lib.Math.Algebra.CayleyDickson
cd ..
for M in \
  E213.Lib.Math.NumberSystems.Real213.Spiral.SpiralLayer \
  E213.Lib.Math.NumberSystems.Real213.Spiral.SpiralCoordinate \
  E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIUnits \
  E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet \
  E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCompletion \
  E213.Lib.Math.Algebra.CayleyDickson.Integer.ImaginaryQuadraticUnitTrichotomy ; do
    python3 tools/scan_axioms.py $M
done
```
Each module reports `N pure / 0 dirty`.
