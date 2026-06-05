# The cycle's intermediate states form a lattice — the four conjectures

*Tier 1.  Engaging Mingu Jeong's refined generative cycle and its four
conjectures.  The cycle: two points, a line; then per cycle — each line → a point
(중간 1), each new point → lines to every non-connected point (중간 2).  Cycle 1
has one growth axis; from cycle 2 the axes multiply and can be chosen within a
cycle.*

## The central finding

The limit is the complete graph `K_n` (trivial); the **intermediate states** are
the content, and they form a **distributive lattice** — the order-ideal lattice
of the cycle's operation poset (Birkhoff).  Counts (computed): intermediate states
per cycle `= 5, 145, vast` (cycle 3 has 63 operations → astronomically many order
ideals).  This lattice — the finite-resolution configurations of the slash's
self-pointing — is the **lattice** of Dynamic Resolution Lattice theory.  The
user's precise description rediscovers *why* the theory is a lattice theory.

## The conjectures, tested

- **Conj. 2 (order-independence from cycle 2) — TRUE, and it is confluence.**
  The operations on distinct growth axes touch disjoint new vertices, so they
  commute (Church–Rosser).  Confluence is exactly §6.2: there is no external time
  axis to order operator before object, so independent distinguishings *must*
  commute — and they do.  Confluence is also what makes the intermediate
  configurations a lattice (join = union of partial states, meet = common part).

- **Conj. 1 (need ordinals / cardinals, not ℕ) — refined: the state space is a
  lattice, not a chain; the limit lattice is uncountable.**  The synchronous
  *cycle* index is ℕ.  But an individual intermediate state is a point in the
  order-ideal lattice (a poset), not a position on a line — so addressing it needs
  a lattice coordinate, not a number.  At the limit, the configurations are the
  paths through the infinite branching, of cardinality `2^ℵ₀`: the "cardinal"
  intuition is correct there.

- **Conj. 3 (no clean termination for cycle > 1) — TRUE in the lattice/ordinal
  sense.**  A cycle completes at the *top* of its order-ideal sublattice, which is
  the **join (supremum) of all its parallel operations** — not a single last step.
  Cycle 1's axis is one point (its completion is a small join); cycle ≥ 2's are
  several independent points, so the completion is the sup of an antichain — a
  *limit*, not a successor.  In ordinal terms the synchronous cycles are ℕ, but
  each cycle's internal closure is limit-like (a join), and only cycle 1 is
  successor-clean.

- **Conj. 4 (growth axes become the cycle's direction) — TRUE, and the axes are
  the simplex dimensions.**  Each independent growth axis is a new vertex, which
  in the free reading is a new orthogonal direction (`AngleStructure/
  SimplexOrthogonality.lean`).  The cycle grows *along these axes* = grows in
  dimension; the growth axes are the `e_i` of `Δ^∞`.

## Why the intermediate stage is the object (and the limit is not)

`K_∞ ≡ point ≡ ∞` is structureless (§6.5): the limit erases distinction, so it
carries no more than a point.  All content lives at finite resolution — the
intermediate states — exactly as DRLT's name says.  "Observe in order, find
patterns" is traversing the order-ideal lattice; its linear extensions are the
admissible observation orders, and its (distributive) structure is the pattern.

## Seed alignment

- §6.2 (operator = object, no external time) ⇒ the operations commute
  (confluence) ⇒ the lattice.
- §5.2 (Nat-style cumulative self-reference) is the per-cycle convergence; the
  multi-axis branching adds the lattice *width* the linear ℕ reading misses.
- §6.5 (the structureless limit) ⇒ the limit is trivial, the lattice is the study.

## Open frontier

The order-ideal lattice is distributive (Birkhoff) and finite per cycle; its size
sequence `5, 145, …` and its growth law are clean enough to pursue ∅-axiom over
`Nat`.  Whether the *limit* lattice (the `2^ℵ₀` configurations) admits a 213-native
description, and how the successor (cycle 1) / limit (cycle ≥ 2) ordinal split
formalizes, is open.
