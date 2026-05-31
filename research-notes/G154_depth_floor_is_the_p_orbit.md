# G154 — the divergence-depth floor IS the P-orbit; depth counts distance from atomicity

**Date**: 2026-05-31. **Status**: cross-frame synthesis + one open ∅-axiom target.
**Depends on**: `DivergenceLadder`, `Mobius213/Px/ConvergentDet`, `every_axis_sees_p`,
`p_orbit_closure_master`, `completeness_without_completeness.md`.

## The observation

The completeness arc built the **divergence ladder**: take a real's convergents,
form the cross-determinant `Wₙ` (discrete Wronskian), and count the finite
differences needed to floor it — that count is the **divergence depth** (φ 1, e 3,
π 6, Liouville ∞; `DivergenceLadder`).  The floor of that ladder — depth 1 — was
characterised in the `DivergenceLadder` docstring as:

> depth 1 ⟺ cross-determinant constant ⟺ the convergents obey a *constant-coefficient*
> (autonomous, `det = 1`) recurrence ⟺ quadratic algebraic (φ, √2 — Pell/Cassini).

Read that last line against the **P-orbit closure** programme (`every_axis_sees_p`,
`p_orbit_closure_master`).  That programme shows the matrix `P = [[2,1],[1,1]]` is
**self-defining**: `χ_P(x) = x² − 3x + 1` (trace `NS = 3`, `det = NS−NT = 1`), and
the recurrence generating its orbit is *forced* by the atomic signature
(`Theory.Atomicity.OrbitForcing`).  The Cassini identity `Wₙ = ±1` for the Fibonacci/
Pell convergents is `convergent_det` (`Mobius213/Px/ConvergentDet`) — `det P = 1`
read along the orbit.

**These are the same object, reached from opposite ends.**

  - From the **analysis** side (completeness arc): start with an arbitrary real,
    measure how far its convergents are from an autonomous recurrence.  The minimum —
    depth 1, `Wₙ` constant — is forced to be `det = 1`, the φ/Pell case.
  - From the **atomic** side (P-orbit closure): start with the forced signature
    `(NS,NT,c,d) = (3,2,2,5)`, derive `P` and its `det = 1` autonomous recurrence.
    Its convergent cross-determinant is constant by construction.

The divergence-depth floor is not *like* the P-orbit; it *is* the P-orbit, seen as
the depth-0 (autonomous) rung of the ladder.  Depth then measures **distance from
atomicity**: how many non-autonomous (polynomial-coefficient) layers a real's
recurrence sits above the one self-defining autonomous recurrence the framework
forces.

## Why this is more than a restatement

Three independent characterisations of "depth 1" coincide, and each was proven in a
different sub-tree with no reference to the others:

| Frame | "depth 1 / floor" object | Lean |
|---|---|---|
| divergence ladder (analysis) | `Wₙ` constant ⟺ `reachesFloor` at the cross-det level | `DivergenceLadder.const_reaches_floor` |
| convergent geometry (number theory) | `det = 1` Cassini `Wₙ = ±1` along the orbit | `ConvergentDet.convergent_det` |
| atomic forcing (213 foundations) | `det P = NS − NT = 1`, orbit recurrence forced | `OrbitForcing`, `CharPolySelf` |

That three sub-trees, built for unrelated purposes, land on `det = 1` as *the* floor
is the kind of multi-frame convergence the framework treats as structural evidence
(cf. `every_axis_sees_p`: every reading projects onto `{NS,NT,det} = {3,2,1}`).  The
depth ladder adds a **new axis** to that catalog: not just "every axis sees P" but
"P is the *bottom* of the resolution-depth axis — the autonomous fixed point every
non-autonomous real is measured against."

## The reading: depth = order of departure from self-definition

Restate the depth hierarchy in P-orbit language:

  - **depth 1** — autonomous, `det = 1`: the recurrence *is* P (up to conjugacy),
    self-defining, needs no external coefficient.  Quadratic irrationals.  This is
    the only rung the atomic signature forces directly.
  - **finite depth `d`** — the recurrence has *polynomial* coefficients of degree
    `d − 2` (P-recursive / holonomic): e (coeff `n+1`, degree 1, depth 3), π
    (degree 4, depth 6).  The recurrence is no longer autonomous; it needs `n` as an
    external dial.  Depth counts the polynomial degree of that dial, plus the two
    base rungs.
  - **depth ∞** — no polynomial-coefficient recurrence: Liouville.  Infinitely far
    from the autonomous floor.

So **depth is the order of the polynomial by which a real's generating recurrence
departs from P's autonomous self-definition.**  Algebraicity (depth 1) = needing no
external dial = exactly the no-exterior condition (`05_no_exterior` §5.1) read at the
recurrence level: the autonomous recurrence has no operand to dial.  Transcendence
of finite depth = needing a *polynomial* dial; transcendence of infinite depth =
needing an unbounded one.

This is a sharper statement of the completeness arc's thesis.  The arc said
"algebraic = closed-form modulus, transcendental = deferred."  In P-orbit language:
**algebraic = the recurrence is the framework's own forced autonomous one;
transcendental = the recurrence needs an external polynomial dial, of degree =
depth − 2.**

## Open ∅-axiom target (the brick this note proposes)

Everything above is assembled from *existing* theorems read together; the synthesis
itself is not yet one Lean statement.  The promotable brick:

> **`depth_floor_is_det_one`** — a sequence `s` with `reachesFloor s` *at the
> cross-determinant level with floor value 1* satisfies the autonomous Pell/Cassini
> recurrence step, i.e. its convergents lie on a `P`-orbit (`pellNormStep`-invariant).

Concretely: connect `DivergenceLadder.const_reaches_floor` (the floor exists) to
`Mobius213PellInvariant.pellNormStep` (the `det = 1` step) by showing that a constant
cross-determinant of value 1 *is* the Cassini invariant, hence the convergents are a
P-orbit.  This would make "depth-1 floor = P-orbit" a theorem rather than a docstring
coincidence, and would be the formal hinge between the analysis-side ladder and the
atomic-side forcing.

Risk / scope: `Wₙ` in `DivergenceLadder` is abstract (`Nat → Nat`); the P-orbit is
`Int`-valued (`pellNormStep` over `Int213`).  The bridge needs the sign-free Nat
reading of `Wₙ = ±1` matched to the Cassini `a² + 1 = a·b + b²` form — the same
Int→Nat wall cleared for `PellFibCutBridge` (additive routing, no `Int` subtraction).
Estimated one focused session.

## Second insight (smaller, for a later note)

The depth ladder and the **Cayley–Dickson tower** (`cd_tower_polarization.md`,
`tower_atlas.md`) are both "property-loss towers" — CD loses commutativity →
associativity → alternativity → composition as it climbs; the depth ladder gains a
polynomial-coefficient layer per rung.  Both bottom out at a 213-forced floor (CD at
the `(NS,NT)` base algebra; depth at P's autonomous recurrence) and both have the
*same* `5 = d = NS + NT` as the controlling discriminant (CD norm-composition layer
count; depth-ladder conic discriminant `disc P = 5`).  Whether these are two readings
of one tower (as `tower_atlas` argues for the P-orbit towers) or a genuine coincidence
is open — flagged here, not pursued.
