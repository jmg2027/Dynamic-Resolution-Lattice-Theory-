# RESOLUTION_LIMIT_SPEC

Canonical reading on cardinality, infinity, and the count-Lens
readout `N_U` within 213.

This document is mechanical-spec level: language is minimised,
metaphor and value-judgment are excluded.  It is the source of
truth.  When `CLAUDE.md`, `seed/AXIOM/`, narrative docs, or Lean
file docstrings drift from this spec, this spec wins.

## Section 0 — T0 (Raw) layer commits to nothing about cardinality

The 213 axiom set (`seed/AXIOM/02_statement.md` §3.3) explicitly excludes from
its commitment list: size, cardinality, finiteness, infinity, order,
hierarchy, set/element relation, observer, space, perception.

Raw is an inductive trajectory carrier, not a set.  At the T0 layer
no cardinality predicate is defined.  "Finite" and "infinite" are
NOT properties of Raw — they are outputs of specific lens
applications (`seed/AXIOM/02_statement.md` §3.3, `Math/Infinity/LensCardinality
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

## Section 2 — N_U as four-Lens convergence

The count-Lens at fractal level 2 yields the same numerical readout
`N_U = d^(d²) = 5²⁵ = 298023223876953125` under four independent
Lens applications:

  1. **Lean formalization**: fractal lens cardinality at level 2.
     `Physics/Foundations/NUniverseFromFractal.lean`:
     `N_universe := d^(d²) = lens cardinality at fractal level 2`.

  2. **Combinatorics**: K₂₅ graph coloring count.
     `Physics/Foundations/FractalLensCardinality.lean`: coloring
     count at K_{25} (d² vertices, d colors) = d^(d²).

  3. **Geometry**: rank-2 tensor degrees of freedom over base
     resolution d=5.  Tensor has d² = 25 components; each carries
     d = 5 independent states; total = 5^25.

  4. **Type theory**: maximum injective projection space at d=5
     resolution.  Beyond depth N_U, projection induces structural
     collision (aliasing); ∅-axiom type checker reduces to noise.

These four readings are distinct Lens applications converging on
the same value.  The observation *is* the convergence; N_U is not
a universe constant nor an axiomatic cap — it is what the
count-Lens reads at fractal level 2 with the forced shape
parameters.  Documents and Lean files cross-reference all four
readings rather than privilege one.

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
