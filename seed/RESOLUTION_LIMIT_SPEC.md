# RESOLUTION_LIMIT_SPEC

Canonical reading on cardinality, infinity, and the constant N_U
within 213.  Replaces the prior "Finitism is forced" framing.

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

## Section 2 — N_U as multi-domain convergent invariant

The constant `N_U = d^(d²) = 5²⁵ = 298023223876953125` arises
independently in four mathematical domains, all yielding the same
value.  This is mechanical justification for treating N_U as a
**system invariant**, not an axiomatic cap.

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

These four framings are not synonyms — they are distinct
mathematical objects in distinct domains that *converge* on the
same value.  Convergence across independent domains is the
strongest available evidence of structural invariance.

Refactoring directive: documents and Lean files must cross-
reference all four framings rather than privilege one.  No single
domain "defines" N_U; the invariant is the convergence itself.

## Section 3 — Resolution limit is a structural invariant (not "finitism")

The phrase "Finitism is forced (not chosen)" overstates by importing
the ZFC dichotomy "finite vs infinite" and electing one side.  The
correct 213-internal statement:

> **Resolution limit is a structural invariant emerging from
>   four-domain convergence at d=5.  Below resolution N_U, lenses
>   project injectively; beyond, structural collision aliases
>   trajectories together at type level.  Both potential infinity
>   (unbounded inductive trajectories) and constructive infinity
>   (Cantor tower, Bishop reals) are admitted; only completed-
>   infinity equality (limit = exact value via propext-quotient)
>   is structurally absent.**

Equivalent shorter forms acceptable:
  - "Cardinality and finiteness are lens outputs."
  - "N_U is a cohomological invariant, not a cap."
  - "ZFC equality between trajectory and limit requires propext;
     ∅-axiom regime does not provide it."

## Section 4 — Refactoring directives (status: completed)

When this spec was first written (2026-04), the following directives
were proposed.  All five have since been applied; this section is
retained as historical record of the integration.

  1. ✓ **CLAUDE.md** — "Finitism is forced" section replaced with a
     pointer to this spec.  (Currently: §"Resolution limit is
     structural".)

  2. ✓ **DyadicTrajectory.lean** docstrings — "ZFC fiction" wording
     replaced with "structural inequality preserved" framing
     matching §1.

  3. ✓ **`seed/AXIOM/02_statement.md`** §3.3 — cross-reference to
     this spec added.

  4. ✓ **Lean formalization** — `lean/E213/Lib/Math/ResolutionLimit
     .lean` types `N_U` + the 4-way convergence + Cantor / Cauchy
     theorems cross-references.  ∅-axiom + 213-native verified.

  5. ✓ **Narrative docs** (`books/`, `guide/`) — "completed infinity
     rejected" / "finitism" wording swept and replaced with §3
     framing.

## Section 5 — Why this spec, in two sentences

213 is attacked most often on the infinity question, and even the
originator and core contributors find it hard to keep the position
straight.  Locking the spec at mechanical-spec level — backed by
Lean formalization — removes the ambiguity that creates the
attacks.
