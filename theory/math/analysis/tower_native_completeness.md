# Tower-native completeness — completability is a comparison of two growth-axes

**Status**: Closed.  Source of truth (all ∅-axiom):
`lean/E213/Lib/Math/Real213/{CrossDetOvertake, LiouvilleModulus, TowerNativeCompleteness}`,
`lean/E213/Lib/Math/Cauchy/{DepthClosure, DepthCoordGenerator, DepthCeilingResidue}`.

## Overview

A Real213 real is a decision procedure against ℚ that completes by a *modulus*; the
constructed-modulus mechanism (`holonomic_modulus.md`) reduces "does this real
complete freely?" to a single inequality on the convergents' **cross-determinant**
`W_i = a_{i+1}d_i − a_i d_{i+1}` against the **denominator** `d` —
`Htel_of_crossdet`'s smallness condition

> `i·(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`   (`CrossDetSmall W d`).

Both sides are objects *inside* the resolution tower (`completeness_without_completeness.md`).
So the classical, external "irrationality measure" is replaced by an internal
comparison of two growth-axes.  This chapter closes that comparison: it stratifies
completability by where the cross-determinant axis sits relative to the denominator
axis, shows the finite-coordinate trajectories form a class closed under the tower's
operations, exhibits a generator that realizes every coordinate, and ties the
top-lessness of the tower to the residue of pointing.

## Lean source

| File | PURE / dirty | Content |
|---|---|---|
| `Real213/CrossDetOvertake.lean` | 10 / 0 | the boundary: `CrossDetSmall`, below ⟹ free, the overtake break |
| `Real213/LiouvilleModulus.lean` | 13 / 0 | Liouville: `W = d`, factorial denominator dominates ⟹ free modulus |
| `Real213/CrossDetEqDenom.lean` | 3 / 0 | the `W = d` rung: one theorem behind both e and Liouville |
| `Real213/GeometricThreshold.lean` | 7 / 0 | the sharp growth-rate boundary: geometric `W=r^i` over `d=q^i` free iff `r < q` |
| `Cauchy/DepthClosure.lean` | 16 / 0 | finite-coordinate class closed under `×` and the exponent axis |
| `Cauchy/DepthCoordGenerator.lean` | 10 / 0 | the tower as a coordinate system, generated top-down |
| `Cauchy/DepthCeilingResidue.lean` | — | the tower has no top = the residue of pointing |
| `Real213/TowerNativeCompleteness.lean` | — | `tower_native_completeness_program`, the five bundled |

Builds under the `E213.Lib.Math.Real213` and `E213.Lib.Math.Cauchy` umbrellas.

## Narrative

### The reframing

In the tower a real is not a *point* but a **divergence trajectory**: the
cross-determinant `W`, its ratio, its differences, descending the resolution axes to a
constant floor (`completeness_without_completeness.md`).  Each trajectory has a
coordinate.  `Htel_of_crossdet` says the trajectory carries a free modulus when its
cross-determinant axis stays below the denominator axis.  Completability is therefore
a relation between two tower-internal growth-axes, read off the coordinate — there is
no set of arbitrary reals to quantify over, only trajectories.

### The boundary (`CrossDetOvertake`)

Over the *fixed* single-exponential denominator `d_i = 2^i`, the position of the
cross-determinant decides completability:

  - **below ⟹ free** (`crossdet_small_total_modulus`): when `CrossDetSmall` holds, the
    smallness feeds `Htel_of_crossdet` then `rate_total_modulus`, giving the total
    modulus `N(m,k) = k+2`.  The free bottom is concrete — a **constant**
    cross-determinant `W_i = 1` (the det-one floor) satisfies `CrossDetSmall` against
    `2^i` (`const_crossdet_small`, since `i ≤ 2^i`);
  - **above ⟹ broken** (`overtake_breaks`): if the cross-determinant overtakes the
    *next* denominator (`d_{i+1} ≤ W_i`, `i ≥ 2`), the smallness condition is false.
    The witness `dexp_overtakes_denom` is the **double exponential** `W_i = 2^{2^i}` —
    the same object whose ratio-axis floor never exists (`DepthDoubleExp.dexp_not_const`)
    — which overtakes `2^i` via `2^{i+1} ≤ 2^{2^i}` (because `i+1 ≤ 2^i`).

`completability_boundary` bundles the two regimes.  The overtake falsifies the
*sufficient* bridge; it is the honest tower-internal boundary, not a proof that no
modulus whatsoever exists.

Between the constant and the double-exponential the boundary is a precise **growth-rate
threshold** (`GeometricThreshold`).  Over a geometric denominator `d_i = q^i` with a
geometric cross-determinant `W_i = r^i`, `CrossDetSmall` holds for all `i ≥ 1` iff the
cross-determinant grows *strictly* slower than the denominator: `r < q` (`r + 1 ≤ q`,
`geom_crossdet_small`).  The threshold is `r < q`, **not** `r ≤ q` — the equal-rate
case `r = q` already fails, because the polynomial factor `i(i+1)` on the
cross-determinant side is linear in `i` while the single extra denominator factor `q`
is only linear in `q`.  Matching the denominator's exponential rate is not enough; a
strong overtake `q^2 ≤ r` breaks it through the same `overtake_breaks` at `i = 2`
(`geom_crossdet_overtake`), and `geom_completability_boundary` bundles the sharp
boundary.  This sharpens the engine `succ_pow_ge` (`r^{n+1} + (n+1)·r^n ≤ (r+1)^{n+1}`,
the binomial first two terms) that absorbs the polynomial factor into one base
increment.

### Liouville is tame on this axis (`LiouvilleModulus`)

On the value axis the Liouville exponent `k!` is depth-∞ (`DepthLiouvilleCoord`:
`diff(k!) = k·k!` never floors), so a Liouville number looks maximally pathological.
The cross-determinant axis says the opposite.  Present the Liouville constant
`Σ_j c^{-j!}` by the recurrence with growth factor `g_k = c^{k·k!}`:

> `liouDen c 0 = c`,  `liouDen c (k+1) = g_k · liouDen c k`  (`= c^{k!}`),
> `liouNum c 0 = 1`,  `liouNum c (k+1) = g_k · liouNum c k + 1`.

Then the cross-determinant **collapses to the denominator** — `liou_cross_det`:
`liouNum_{k+1}·liouDen_k = liouNum_k·liouDen_{k+1} + liouDen_k`, i.e. `W_k = liouDen_k`
— exactly the e pattern (`euler_cross_det`).  The factorial denominator grows so fast
(`g_k = c^{k·k!} ≥ k+1`, `succ_le_g`, reusing `two_pow_ge_succ`) that `CrossDetSmall`
holds (`liou_crossDetSmall`), so `liouville_total_modulus` gives the free modulus
`N(m,k) = k+2`.  `liouville_W_eq_denom_coordinate` is the adjudication: `W` equals `d`,
`d`'s exponent **is** the factorial (`liouDen_closed`, `liouDen_k = c^{k!}`), and the
factorial sits at recursion-coordinate ratio-depth 1 one tier down (`ratioLift_fact`,
`k! ↦ k+1`).  So the recursion-coordinate of `W` coincides with that of `d` while `d`
strictly dominates — the comparison comes out `W ≤ d`, and a Liouville number completes
exactly like e.  The value-axis depth-∞ is irrelevant to completability.

### The W-relation rungs (`CrossDetEqDenom`)

The cross-determinant's relation to the denominator sorts the trajectories into rungs,
all read through the one bridge `CrossDetSmall ⟹ free`:

  - **`W` constant** — the algebraic det-one floor (`DepthFloorDetOne`, φ/√2 with
    `W = 1`); `const_crossdet_small` witnesses `CrossDetSmall` against a fast
    denominator;
  - **`W = d`** — the self-similar rung (e and the Liouville constant); the one theorem
    `crossdet_eq_denom_total_modulus` covers both, with `CrossDetSmall d d` collapsing
    (`i(i+1)+i = i(i+2)`) to a denominator-growth condition, and
    `euler_total_modulus_via_eq_denom` / `liouville_total_modulus_via_eq_denom` the
    one-line instances;
  - **`W ≫ d`** — the overtake (`dexp_overtakes_denom`), where `CrossDetSmall` fails.

So "constant cross-determinant" (algebraic) and "cross-determinant equal to the
denominator" (the two structured transcendentals proven here) are two rungs *inside*
the free region, and the double exponential is the first rung outside it.

### Closure of the finite-coordinate class (`DepthClosure`)

The trajectories of *finite* coordinate form a class closed under the tower's
operations, by the linearity of the difference operator:

  - `diff` is additive on monotone sequences, so every iterated difference distributes
    (`diffN_add`): the finite-difference-depth class is closed under `+`
    (`finDiffDepth_add`, the floor of a sum reached by the deeper summand);
  - a sum of exponents is a **product** of values — `c^{e₁+e₂} = c^{e₁}·c^{e₂}`
    (`expSeq_mul`) — so closure of exponents under `+` is closure of the exponential
    values under `×` (`value_mul_closed`); φ, e, and any finite-coordinate real
    generate a family under multiplication, for free;
  - the **exponent axis** lifts a finite difference depth to a finite ratio depth one
    tier up (`value_finRatio_of_finDiff`, value-height = 1 + exponent-height), and this
    closure **breaks exactly at the exponential** — `twoPow = 2^n` is not of finite
    difference depth (`twoPow_not_finDiff`) and its value `2^{2^n}` has no finite ratio
    depth (`exp_axis_breaks`).

`rate_carrying_tower_closure` bundles the four.  This is holonomic closure made
internal to the resolution tower, with the boundary the same `2^{2^n}` of the overtake
layer.

### The tower is a coordinate system (`DepthCoordGenerator`)

The tower is also a generator: place a coordinate and read off a sequence sitting at
it.  The degree-`d` binomial column `genExp d = (n ↦ binom n d)` realizes
difference-depth `d` for every `d` (`genExp_realizes`, `= binomCol_polyDepth`); its
exponentiation `genValue c d = c^{binom · d}` has finite ratio-depth `d`
(`genValue_floors`); and the `ω^r` tower `expTower c r` realizes every exponential
height, each strictly dominating the whole lower tower (`coord_layer_dominates`) by the
generator recursion `expTower c (r+1) = c^{expTower c r}` (`expTower_succ`).
`tower_is_coordinate_system` bundles these — the `ω^ω` ladder is populated level by
level by explicit sequences.  The finite-coordinate ones are exactly the rate-carrying
class that carries a free modulus (φ, e, the Liouville constant), so each generated
finite coordinate is an actually-completing real.

### The deep tie: the tower has no top (`DepthCeilingResidue`)

Naming "the act of raising the ceiling" is a diagonalisation (`diag_not_in_seq`) — the
same Cantor self-cover (`cantor_general`) that makes the residue of pointing
(`ceiling_reference_leaves_residue`, `ceiling_residue_is_pointing_residue`).  The real-
number tower has no top because pointing has no exterior; its top-lessness **is** the
residue read at the scale of divergence-complexity.  The boundary of constructive
completeness and the surplus of pointing are one object.

### One statement

`tower_native_completeness_program` (`TowerNativeCompleteness`) is the single ∅-axiom
conjunction of the boundary, the Liouville adjudication, the closure, the generator,
and the residue tie.  In one line: **completability reduces to a comparison of two
growth-axes inside the tower, the tower has no top, and its top-lessness is the
residue — so the real line's completability is a stratified, self-generating,
foundation-touching structure, not a yes/no fact about individual reals.**

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `completability_boundary` | `CrossDetOvertake` | over `2^i`: constant `W` free, double-exp `W` breaks |
| `crossdet_small_total_modulus` | `CrossDetOvertake` | `CrossDetSmall` ⟹ total modulus `N=k+2` |
| `liou_cross_det` | `LiouvilleModulus` | the Liouville cross-determinant equals its denominator |
| `liouville_total_modulus` | `LiouvilleModulus` | the Liouville constant carries a free modulus |
| `liouville_W_eq_denom_coordinate` | `LiouvilleModulus` | `W` and `d` share the factorial-tier coordinate, `d` dominates |
| `finDiffDepth_add` / `value_mul_closed` | `DepthClosure` | finite-coordinate class closed under `+` / `×` |
| `value_finRatio_of_finDiff` / `exp_axis_breaks` | `DepthClosure` | exponent-axis closure, breaking at `2^{2^n}` |
| `tower_is_coordinate_system` | `DepthCoordGenerator` | every tower coordinate realized by an explicit sequence |
| `ceiling_residue_is_pointing_residue` | `DepthCeilingResidue` | the tower's top-lessness is the residue of pointing |
| `tower_native_completeness_program` | `TowerNativeCompleteness` | the five, bundled |

## Open frontier

None internal to the program.  The tower-native targets — the overtake boundary, the
Liouville adjudication, closure of the finite-coordinate class under `×` and the
exponent axis, a generator surjective onto the tower coordinates, and the residue tie
— are all closed ∅-axiom.  Two genuinely-classical questions sit *outside* the
tower-native frame and are not claimed here: full num/den closure under `+` and `×`
for arbitrary rate-carrying presentations (the classical holonomic-closure theorem),
and a fully generic ordinal-indexed `coord → cut` map for every `ω^r` position at once.
A fast π representation meeting the rate criterion is the concrete next instance
(`holonomic_modulus.md` frontier).

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Real213 E213.Lib.Math.Cauchy
cd ..
for M in \
  E213.Lib.Math.Real213.CrossDetOvertake \
  E213.Lib.Math.Real213.LiouvilleModulus \
  E213.Lib.Math.Cauchy.DepthClosure \
  E213.Lib.Math.Cauchy.DepthCoordGenerator \
  E213.Lib.Math.Real213.TowerNativeCompleteness ; do
    python3 tools/scan_axioms.py $M
done
```
Each module reports `N pure / 0 dirty`.
