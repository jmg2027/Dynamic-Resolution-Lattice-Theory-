# The lift archetypes: a partial order and its dualities

The seven lift archetypes are not a flat list.  They sit in a **partial order by
lift-cost** and pair up by **duality**, over a single root.  This is the internal
structure of the lift axis of the proof-ISA (companion to the lift/EQUIV split in
`lifts_versus_fold_equalities.md`).

## The root: DIAGONAL is ⊥

DIAGONAL (`lift_diagonal` = `cantor_general` / `object1_not_surjective`) has
**lift cost zero**: the `DIAGONALIZE` instruction *is* the uniform witness — the
anti-diagonal is the residue.  Every infinity-proof (Cantor, Russell, Gödel,
Turing) reduces to it.  So DIAGONAL is the bottom of the order: the most
primitive lift, the one the others are built over.  It is also **self-dual** —
`object1_not_surjective` is simultaneously the diagonal (a residue distinct from
every reading) *and* the GAP (the un-covered surplus).  The residue is the fixed
point of the duality below.

## Dual pair 1 — LOOP ⟷ FLOW  (µ / ν, forward / backward)

- **LOOP** (`lift_loop`, Fermat `a^p ≡ a`; witness `slashNu_final`/induction):
  certify a fixed point by **forward** finite-path induction — *build up* along a
  recurrence.  This is the **µ** (initial-algebra / least-fixed-point) direction.
- **FLOW** (`lift_flow`, `flow_reaches`; the GCD / Ricci flows): reach a fixed
  point by a **monovariant that strictly descends** — *settle down* to a normal
  form.  This is the **ν** (final-coalgebra / greatest-fixed-point) direction.

They are the two directions of one fixed-point principle: LOOP iterates a
recurrence forward; FLOW descends a measure backward.  The repo's own µ/ν mirror
(`Raw` initial algebra vs `slashNu` final coalgebra) is exactly this axis.
Incomparable in cost (each costs one well-founded pass), genuinely mirror.

This duality is now a **theorem** (`Foundations/FlowDuality.flow_reaches_ascending`,
∅-axiom): a measure that strictly *ascends* off fixed points and is *bounded
above* by `B` reaches a normal form — proved by reflecting to
`MonovariantFlow.flow_reaches` (descent) through `μ ↦ B − μ`.  Ascent-under-a-cap
*is* descent of the mirror; LOOP (build up to a cap) and FLOW (settle down) are
one well-founded principle, witnessed by the order-reversal.

## Dual pair 2 — COUNT ⟷ POSITIVITY  (the two quantitative faces of GAP)

Both are GAP read by a **nonnegative-valued Lens** — a quantity that cannot go
below zero, so a forced inequality yields a witness.  They differ only in *which*
nonneg Lens:

- **COUNT** (`lift_count`, Erdős `R(k,k)>2^{k/2}`): the **cardinality** Lens — a
  deficit `Σ|badᵢ| < |codomain|` forces a good element (counting `≥ 0`).
- **POSITIVITY** (`lift_positivity`, Cauchy–Schwarz / sums of squares): the
  **norm/square** Lens — a gap equal to a square (`≥ 0`) forces a bound.

COUNT is "the un-covered surplus, *counted*"; POSITIVITY is "the gap, read as a
*square*."  One residue (GAP), two nonneg readings.  (Hence `pigeonhole` and
`sq_nonneg` are siblings, not unrelated tricks.)

**But this pairing is weaker than LOOP ⟷ FLOW** — an honest asymmetry between the
two dual pairs.  LOOP/FLOW is a *strict* duality: a literal order-reversal
`μ ↦ B − μ` turns one into the other, so they are the *same theorem*
(`flow_reaches_ascending`, witnessed above).  COUNT/POSITIVITY has no such
reduction: their *logical shapes* differ — COUNT is "a comparison `Σ < capacity`
forces a witness to **exist**" (contrapositive / pigeonhole), POSITIVITY is "an
algebraic form `gap = s²` forces an **inequality** directly".  Both read GAP
through a nonneg Lens, but neither reduces to the other; the pairing is a
*two-faces analogy*, not an order-reversal.  So the lift order has (at least) two
*grades* of duality — strict (LOOP/FLOW) and facial (COUNT/POSITIVITY) — which is
itself a fact about the catalog, not a defect of it.

## ORBIT — the quotient

ORBIT (`lift_orbit`, composite Markov uniqueness) collapses a finite window by a
**free group action** onto orbit representatives, leaving a per-instance
realizability residue.  It is LOOP *modulo a symmetry* — induction after
quotienting by a free action — so it sits **above** the LOOP/FLOW pair in the
order (it needs the fixed-point pass *plus* the action's freeness).

## REFRAME — the meta-lift (higher-order)

REFRAME (`lift_reframe`, CRT / the `3c±2` modulus shift) is not a base archetype
but a **transport**: when an archetype fails to fire under one reading, factor a
shared invariant and re-`READ` through the presentation where a *solved*
archetype now fires.  So `REFRAME[X]` operates *on* the order — it relocates a
problem to where `X ∈ {DIAGONAL, LOOP, FLOW, COUNT, POSITIVITY, ORBIT}` applies.
Conditional (needs a prime-power / good factor), and the dual of in-place
monovariant exhaustion.  It is the top, wrapping any base archetype.

## The order

```
                         REFRAME[ · ]            (meta: wraps any base)
                              │
                            ORBIT                (LOOP modulo a free action)
                          ╱       ╲
                  LOOP ⟷ FLOW   COUNT ⟷ POSITIVITY
                    (µ / ν)        (two faces of GAP)
                          ╲       ╱
                          DIAGONAL  = ⊥          (the residue; self-dual)
```

Read upward = increasing lift-cost / dependency.  The two dual pairs are
incomparable (neither µ/ν nor count/square refines the other); each pair is a
mirror, not a chain.  DIAGONAL is below both pairs (the residue they read);
ORBIT is above LOOP/FLOW; REFRAME wraps the whole order.

## Why this matters

"Compile a conquest to a lift archetype" is sharper given the order: locate it on
the **GAP face** (count vs square) or the **fixed-point direction** (µ vs ν),
check whether it needs **ORBIT**'s quotient, and whether it is reachable only
after a **REFRAME** transport.  The Markov kernel `H`, for instance, is localized
to ORBIT-after-REFRAME (a free-action realizability residue reached by a
modulus-shift transport) — a *position in the order*, which is what
`ProofISALifts §H` records.  The order turns "which archetype?" into "where in the
lattice of archetypes?".
