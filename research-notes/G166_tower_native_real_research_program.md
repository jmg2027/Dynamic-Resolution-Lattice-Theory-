# G166 — the tower-native real-number research program

**Date**: 2026-06-01. **Status**: research agenda (open targets, ∅-axiom-shaped).
**Anchors**: `theory/math/analysis/holonomic_modulus.md`,
`Cauchy/{DepthTower,DepthOrdinal,DepthOmegaTower,DepthExponentRecursion,DepthDoubleExp,
DepthLiouvilleCoord,DepthCeilingResidue,DepthFloorDetOne}`, `Real213/RateModulus`
(`Htel_of_crossdet`).

The completeness arc + the modulus generator together turn a classical question —
"which reals admit a good modulus / measure?" — into a question *internal to the
resolution-axis tower*.  This note records the directions that opens, dropping
classical concepts (irrationality measure, countability, halting) entirely.

## The reframing

In the tower a real is not a *point* but a **divergence trajectory**: the
cross-determinant `W`, its ratio, its differences, descending the axes to a constant
floor.  Each trajectory has a coordinate (depth `(h,d) < ω²`; the `ω^r` tower
position).  The bridge `Htel_of_crossdet` says the modulus exists iff

> **the cross-determinant axis stays below the denominator axis**:
> `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`.

Both sides are *tower-internal* objects.  So the classical, external "irrationality
measure" is replaced by an **internal comparison of two growth-axes**.  "Can we
complete an arbitrary real?" is the wrong shape: there is no set of arbitrary reals to
quantify over, only trajectories, and completability is read off the coordinate.

## Targets

### T1 (sharpest) — the exponential-overtake boundary layer

`DepthExponentRecursion` (value-height = 1 + exponent-height) + `DepthDoubleExp`
(`ratioN` cannot cross one exponential layer) say that climbing one axis multiplies
the cross-determinant's growth by an exponential.  Conjecture, ∅-axiom-shaped:

> **rate-carrying (free modulus) holds for trajectories below a critical tower level
> and fails above it — the level where the cross-determinant's exponential growth
> overtakes the denominator's.**

This is a *structural* completeness theorem stratified by tower coordinate, proved by
comparing axis positions — no measure, no LEM.  The autonomous floor
(`DepthFloorDetOne`, det 1, `W` constant) is the trivially-free bottom; the boundary
layer is the genuine content.

### T2 — Liouville's recursion coordinate vs the denominator

Liouville is diff-axis depth-∞ (`DepthLiouvilleCoord`: exponent `k!`) yet has a
*finite recursion coordinate* (`k! ↦ k+1` under ratio).  Its `W` explodes
(`10^{k!}`-scale) but its approximation is super-good.  Tower-native question:

> **does the recursion-coordinate of `W` sit above or below that of `d`?**  That
> comparison — not any measure — decides whether Liouville carries a free modulus.

This is the exact point where "fast rate ⟹ free" and "depth-∞ ⟹ no structure" collide,
and the tower *adjudicates* it by a two-coordinate comparison.  Concrete, closeable.

### T3 — closure of rate-carrying under the tower's operations

Are the rate-carrying trajectories closed under `+`, `×`, and the exponent axis
(`value ↦ c^value`)?  If `+`/`×` close (holonomic closure made tower-native), a whole
family follows from φ and e for free.  The exponent axis is where T1's overtaking
bites — closure should hold up to the boundary layer and break at it.

### T4 — reals generated top-down from a coordinate

The tower is a *coordinate system*, not just a classifier: place a point (a
cross-determinant recurrence, an `ω^r` position) and read off the real it defines.
This gives an ordinal-indexed family of reals — e is one point at depth 3; the tower
populates every level.  A generator `coord → cut` is the constructive form.

## The deep tie (why this is foundational, not just analysis)

`DepthCeilingResidue`: naming "the act of raising the ceiling" is a diagonalisation =
the residue (`cantor_general`).  The tower has no top; the real-number tower **is the
residue's self-covering read at the scale of divergence-complexity**.  So the limit of
constructive completeness and the surplus of pointing are one object — completeness's
boundary is the residue.  T1's "critical layer" and the ceiling/`ε₀` structure are the
same wall seen from the analysis side and the foundational side.

The program, in one line: **completeness reduces to a comparison of two growth-axes
inside the tower, the tower has no top, and its top-lessness is the residue — so the
real line's completability is a stratified, self-generating, foundation-touching
structure, not a yes/no fact about individual reals.**
