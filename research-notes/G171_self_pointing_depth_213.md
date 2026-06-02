# G171 — the depth ladder, read in 213 (self-pointing, residue, floor)

**Date**: 2026-06-02.  **Status**: 213-native re-reading of the divergence-depth work
(`DepthAperyCubic`/`DepthQuadraticGeneric`/`CasoratianStep`), + one ∅-axiom capstone
(`DepthResidueFloor`, 2 PURE).  Standard-math vocabulary (Apéry, irrationality measure,
Casoratian, Zagier sporadic) is set down here on purpose; the same facts are described in
213 primitives.

## The move

Everything built this marathon is, stripped of imported frames, about **one operation**:

    diff s = (n ↦ s(n+1) − s n)

`diff` is a **pointing event**.  Given a path one can point at (a sequence), `diff` points
again — at *how the path changes* — reading the previous level's residue as a fresh path.
This is not a new structure; it is pointing applied to the trace of pointing
(`01_residue.md §1.2`: "the next pointing has new material to work on").  `liftK k` is `k`
successive such events.

**Depth** is then the count: how many re-pointings until the path **stops moving**
(reaches a constant — the floor).  `polyDepth d s` records "the `d`-th re-pointing first
coincides with itself."

## The two ends are already in the canon

- **Top (no closure).**  `DepthCeilingResidue`: point at "the whole act of pointing" and
  the diagonal escapes — the surplus reappears one level up, the iteration **never
  settles**.  This is the residue itself (`object1_not_surjective`, Cantor in temporal
  guise; `05_no_exterior` §5.1: pointing has no exterior).  **Infinite depth = the
  residue.**

- **Floor (immediate closure).**  `DepthFloorDetOne`: the cross-determinant `W = 1` of the
  `P = [[2,1],[1,1]]` orbit (det `1`, the Cassini invariant), fixed point φ.  This is the
  **self-same rule** — its step does not depend on `n`; re-pointing returns it unchanged.
  **Depth 0.**  It is the residue's own algebraic image (`05_no_exterior` §5.6, `G29`):
  `P(φ) = φ`, the self-reference that closes the instant it is made.

## What this marathon added: the ladder between them

`DepthResidueFloor.self_pointing_depth_ladder` (∅-axiom):

    P/φ floor : 0  →  e : 1  →  ζ(2) : 2  →  ζ(3) : 3

Read in 213, the depth is **how far a rule's `n`-dependence has drifted from pure
self-reference**:

- the floor `P`/φ *is* its own fixed point — the rule applies identically at every step
  (degree 0 in `n`), the closure of self-reference with no drift;
- each rung adds exactly one degree of `n`-dependence before the re-pointing settles:
  e's step `n+1` (degree 1), ζ(2)'s degree-2 step, ζ(3)'s degree-3 step.

The whole degree-2 band (every `A·n²+B·n+C`) closes at depth 2 uniformly
(`DepthQuadraticGeneric.quadratic_polyDepth`) — the rung is a band, not a point.

## The relocation (the actual 213 content)

In the imported frame, "ζ(3) has a degree-3 recurrence" is a fact *about the limit ζ(3)*.
In 213 the same fact says something different and sharper:

> the **limit** ζ(3) is residue — never pinned by any finite (rational) reference, sitting
> with the surplus no pointing catches; but the **rule** that generates its approximations
> is **3 self-pointings from the floor**.

So the count `3` is not a property of the unpinnable limit; it is the **distance of the
generating-rule from the residue's own algebraic floor `P`/φ**.  The residue lens moves
"degree 3" off the limit and onto the rule's drift-from-self-reference.  A residue-limit,
produced by a finite-depth rule — the resolution structure made explicit: finite-depth
rule, residue limit.

This is why the `casoratian_step` law matters here (`CasoratianStep`): when two pointings
(two solutions) are crossed, the **middle, self-referential coefficient cancels** and only
the boundary coefficients (`c₂`, `c₀` = `aperyTop`, `aperyBot`) propagate.  The interior
self-reference drops; what carries the cross-determinant is the edge.  A no-exterior
signature at the level of the rule.

## The closure dichotomy (finite vs residue)

The depth ladder realises the residue dichotomy directly:

- **closes in finite steps** ⟺ the rule is a discrete polynomial — its self-pointing
  terminates (these are exactly the finite-`polyDepth` paths; the floor and rungs above);
- **never closes** ⟺ the residue (`infinite_depth`; e.g. the geometric `2ⁿ`,
  `geom_infinite_depth` — re-pointing keeps producing new distinction).

"Has finite depth" is not "has an exterior reference that catches it" — there is no
exterior.  It is the path's **own** structure folding onto itself in finitely many
self-pointings.  The floor `P`/φ is the limit case: one fold and it is already itself.

## Honest flags (don't force)

- The rung counts land on `{2, 3}` for ζ(2), ζ(3); the atomicity is `(NS, NT) = (3, 2)`
  and `{2,3}` are the free-factor orders of `PSL(2,ℤ) = ℤ₂*ℤ₃` (`G171_modular_tower_axes`).
  Whether the depth-`{2,3}` and the atomic `{NT,NS}` / `ℤ₂*ℤ₃` are the *same* `{2,3}` is
  **not established** — the depth is just the rule's `n`-degree `k` for `ζ(k)`.  Recorded as
  a question, not a map; forcing it would be the "stereotype matching" / "forcible map"
  failure mode.
- "Depth = self-pointing-distance from the floor" is a *reading* of the count, not an extra
  claim about the numbers.  It carries no irrationality content (degree is incidental to
  irrationality — see `G171_apery_zeta_tower`).  Its value is that it places the marathon's
  results inside the residue/no-exterior canon rather than beside it.

## Anchors

`DepthResidueFloor.{floor_polyDepth0, self_pointing_depth_ladder}`,
`DepthFloorDetOne.{W, W_isConst}`, `DepthCeilingResidue.ceiling_reference_leaves_residue`,
`DivergenceLadder.infinite_depth`, `seed/AXIOM/05_no_exterior.md` §5.1/§5.6,
`research-notes/G29_residue.md`.
