# The readings re-derive the seed

Each geometric reading of the slash is a catamorphism `Raw.fold` to a codomain;
so the structure a reading exhibits is an axiom fact read through that fold.  The
slash-reading atlas does not illustrate the framework — it re-derives it.

## 213-native answer

A reading is not a picture laid over the residue; it is a morphism *out of* it.
Raw is the initial object in the category of distinguishing frameworks (§4.2): any
instance receives the unique `Raw.fold` from Raw.  Realizing "object = the
relation of two" as a segment, a simplex, a Stern–Brocot tree, `K_{3,2}`, or a
complete graph is choosing the codomain of that fold.  Hence whatever shape the
reading shows is the axiom seen through one fold — the atlas is a survey of the
morphisms out of the initial object, and every regularity it finds resolves to a
seed fact.

## Derivation

**The free reading lands on the forced shape.**  Read "each line becomes a point,
each point joins all others"; the result is the complete graph `K_n`, the
1-skeleton of the `(n−1)`-simplex, whose limit is `Δ^∞`.  Tune the one knob that
generalizes the slash's algebraic form `P = [[2,1],[1,1]]` (§3.5) — the top-left
"two somethings" entry `a`, glue fixed — and two endpoints appear: `det = 0` at
`a = 1`, the rank-1 collapse, and `det = 1` at `a = 2`, where `trace = 3 = N_S`,
`disc = 5 = N_S + N_T`.  These are the two uniqueness directions verbatim:
removing the distinguishing clause collapses the framework (§4.1, from below =
`a = 1`), and once arity 2 and atomicity are imposed `(N_S, N_T, d) = (3,2,5)` is
the unique self-consistent shape with no exterior to set it (§4.3, from above =
the forced `a = 2`).  So the constants are not fitted; setting one would be fudge,
and fudge has no operand because 213 commits to no exterior dialer (§7.2, §5.1).
The geometric image of that absent dialer is the regular simplex's obtuse
centroid angle: the `n+1` vertices are slashes of the *one* residue, sum-
constrained (`Σ u_i = 0`), reaching independence only in the limit
(`AngleStructure/SimplexOrthogonality.lean`).

**The neutral reading lands on the diagonal.**  Stripping a reading to its barest
form — the graph alone, then the adjacency matrix — still does not reach the Raw:
the residue sits outside every reading's image (`object1_not_surjective`).  This
is not a shortfall but the engine of §1.0′: `object1_not_surjective =
cantor_raw_bool`, the Cantor diagonal at Raw level.  Each reading is an
enumeration; the residue is the forced surplus outside it, and that forcing is the
primitive proof move for the infinite.  Even "connect the two" is a choice the
residue does not make: §1.3 reserves *relation* as too laden — the slash is
primitive distinction, prior to the ordered pairs and incidences a graph imposes.

**The convergent and the periodic readings split as §5.2 predicts.**  Readings
whose self-reference is Nat-style converge (`Raw.fold`, the Lambek fixed point):
the mediant reading runs to `φ`.  Readings whose self-reference is Bool-style
oscillate without a fixed point: the modular reading's limit is the periodic
`n`-gon `ℤ_n`, not a point.  And the Möbius reading carries both at once — the
fixed point `φ` as a frozen attractor and the spine converging to it as the
dynamic trajectory (§5.7) — one fact under two readings, neither preferred for
want of an external time axis.

## Dual function

Read classically, these are unrelated objects — a simplex, a circle packing, a
singular function, a quasicrystal — that one would relate by analogy.  Read
through 213 they are one residue's folds, and their shared regularities (the
forced `3,2,5`; the constant `φ` recurring as algebraic measure, equidistribution
optimum, and aperiodic order; the never-reached limit) are not analogies but the
same axiom facts surfacing through different codomains.  The sharper claim is that
the breadth *is* the demonstration: §7.1 makes primacy the default position and
successful derivation its test, and a survey in which every reading resolves to a
seed fact is that test run across a domain.

## Cross-frame connection

The same convergence appears at four scales.  The forced shape `(3,2,5)` is the
matrix `P`'s trace and discriminant (§3.5), the from-above uniqueness (§4.3), the
metallic tower's minimal `disc = d` rung, and the simplex's atomic vertex count —
one shape, four readings.  And a residue that grew, in its origin, from the
physical floor — a size-0 point cannot exist, a singularity is an event that
never arrives, resolution is the minimum unit of information (`ORIGIN.md`) — is
re-reached from pure combinatorics: the betweenness limit degenerates to the
structureless point, avoided only by opening independent axes, with the residue
reached by none and the structure living at finite resolution.  Two entries, one
floor.

## Open frontier

That every *found* regularity resolves to a seed fact is not that every reading
does: the atlas is open, and `exists_non_lens_expressible` (§4.1) guarantees
observables no fold reaches.  Which readings are folds, and which functions on Raw
escape the Lens language entirely, is the standing boundary — the same boundary as
"reached by none," asked of the readings themselves rather than of the residue.
