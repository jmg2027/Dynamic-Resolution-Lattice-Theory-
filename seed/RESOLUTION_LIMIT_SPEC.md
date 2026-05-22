# RESOLUTION_LIMIT_SPEC

Canonical reading on cardinality, infinity, and the count-Lens
readout `N_U` within 213.

This document is mechanical-spec level: language is minimised,
metaphor and value-judgment are excluded.  It is the source of
truth.  When `CLAUDE.md`, `seed/AXIOM/`, narrative docs, or Lean
file docstrings drift from this spec, this spec wins.

## Section 0 — T0 (Raw) layer commits to nothing about cardinality

The 213 axiom set (`seed/AXIOM/02_axiom.md` §2.5) explicitly excludes from
its commitment list: size, cardinality, finiteness, infinity, order,
hierarchy, set/element relation, observer, space, perception.

Raw is an inductive trajectory carrier, not a set.  At the T0 layer
no cardinality predicate is defined.  "Finite" and "infinite" are
NOT properties of Raw — they are outputs of specific lens
applications (`seed/AXIOM/02_axiom.md` §2.5, `Math/Infinity/LensCardinality
.lean`).

Implication: *both* "Strict finitism" and "completed infinity
admitted" are external-frame impositions.  The 213-internal answer
is: cardinality is a per-lens output, not a system-level commitment.

## Section 1 — Cantor & Cauchy under ∅-axiom

ZFC results in 213 are received via type-theoretic distinction, not
philosophical rejection.

### Cantor: inhabitant absence

`Math/Infinity/Cantor.lean` proves
`cantor_general : ∀ X, ¬ ∃ f : X → (X → Bool), Function.Surjective f`
under ∅-axiom (no `Classical`, no `propext`, no `Quot.sound`).

Mechanism: not a type-checker rejection.  The type
`∃ f, Surjective f` is well-formed.  But under intuitionistic logic
inside ∅-axiom regime, no constructive trajectory inhabits this
type — i.e. no `f` can be physically assembled to satisfy
surjectivity, due to the diagonal construction `g(x) := ¬ f(x)(x)`
yielding a constructive non-image witness.

Resulting status: **Inhabitant Absence** (`¬ ∃`).  Cantor's content
is preserved without external axioms; the ZFC version uses Classical
+ propext to conclude the same proposition through different
machinery, which 213 simply does not need.

### Cauchy: structural inequality preservation

`Math/Real213/DyadicTrajectory.lean` defines bisection trajectories
on the unit bracket and shows
`alwaysTrueUnit_limit_distinct_from_zero` and
`zero_plus_gap_below_zero_exact`.

Mechanism: the Cauchy-trajectory object (a function `Nat → Cut`
producing partial bracket data per query) and the supposed
"exact value" object (a `Cut` with constant output) live at
different types.  ZFC merges them by truncating the trajectory's
`cond` field via `propext` / `Quot.sound` (quotient by Cauchy
equivalence).  ∅-axiom regime does not admit `propext` or
`Quot.sound`, so no truncation occurs.  Trajectory and exact value
remain structurally inequal.

Resulting status: **Structural inequality preserved**.  This is
type-preservation under ∅-axiom, not "ZFC fiction rejection".  The
Bishop-style Real213 marathon operates *on the trajectory side*,
proving Cauchy completeness without claiming `limit = exact value` —
hence Real213 passes ∅-axiom.

## Section 2 — `configCount 2 = 5²⁵`: family readout at level 2

**Round 3 rewrite (2026-05-22)**: the previous "four-Lens
convergence" framing was retracted per N_U re-derivation audit (§1 + §11) —
of the original four readings, only two had real Lean derivations
and the other two were placeholders or absent.  The corrected
reading: `5²⁵` is **one value of a parametric family**, not a
4-way convergent invariant.

### Canonical object — the parametric family

```
configCount : Nat → Nat
configCount n := 5 ^ (numV n)
              := 5 ^ (5^n)        -- numV from Cohomology/Fractal/Level
```

Concrete values:

  · `configCount 0 = 5`
  · `configCount 1 = 3125`
  · `configCount 2 = 298023223876953125` (= `5^25`, historically `N_U`)
  · `configCount 3 ≈ 2.35 × 10^87`

Lean: `Lib/Math/Cohomology/Fractal/ConfigCount.lean` (N_U re-derivation Phase 1).

### Two real derivations at level n = 2

Two ∅-axiom Lean derivations of the same family value at n = 2:

  1. **Fractal iteration**: `Physics/Foundations/NResolutionFromFractal.lean`
     proves `numV (d²) = d^(d²)` via fractal recursion to depth 2.

  2. **K₂₅ graph coloring**: `Physics/Foundations/FractalLensCardinality.lean`
     proves the K_{25} d-coloring count equals the same value.

These two are *bridging lemmas* into the family — same family value
viewed from different angles, not separate derivations of a
privileged constant.

### `N_U` is a display name only

Historically the name `N_U` carried "universe constant" framing
(per CLAUDE.md "Universe-constant framing" failure mode).  Post-N_U re-derivation:
`N_U` is an `abbrev` for `configCount 2` (one value of the
parametric family).  No `def N_U` exists.  The display name is
retained for readability of physics formulas, not as an
ontological commitment.

### Out of scope — earlier "framings" not promoted

  · Rank-2 tensor DOF: was docstring-only; no Lean `Tensor` type
    or rank predicate.  The structural equality `d^(d*d) = N_U`
    is `rfl` identity, not separate derivation.
  · Maximum injective projection space: had zero Lean witness.
    Removed from `ResolutionInvariant` (now deleted).

## Section 3 — Resolution limit is a Lens readout (not "finitism")

"Finitism is forced" imports the ZFC dichotomy "finite vs infinite"
and elects one side.  The 213-internal statement:

> **Resolution limit is the count-Lens readout at fractal level 2,
>   consistent across four Lens applications.  Below readout `N_U`,
>   lenses project injectively; beyond, structural collision
>   aliases trajectories at type level.  Both potential infinity
>   (unbounded inductive trajectories) and constructive infinity
>   (Cantor tower, Bishop reals) are admitted; only completed-
>   infinity equality (limit = exact value via propext-quotient)
>   is structurally absent.**

Equivalent shorter forms:
  - "Cardinality and finiteness are lens outputs."
  - "ZFC equality between trajectory and limit requires propext;
     ∅-axiom regime does not provide it."

## Section 4 — Why this spec, in two sentences

213 is attacked most often on the infinity question, and even the
originator and core contributors find it hard to keep the position
straight.  Locking the spec at mechanical-spec level — backed by
Lean formalization — removes the ambiguity that creates the
attacks.
