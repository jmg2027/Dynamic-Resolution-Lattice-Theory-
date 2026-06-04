# G171 — do the merged G150 (McKay/icosian) concepts help the completability thread?

**Date**: 2026-06-01.  **Status**: synthesis + one ∅-axiom unification capstone.
**Source of truth**: `lean/E213/Lib/Math/FiveFloorUnification.lean` (1 PURE).
**Anchors**: the merged `CayleyDickson/Tower/{MobiusPIcosian, MckayADECensus,
SeedUnitGovernance}` + `research-notes/G150`, against this thread's
`Real213/{FloorReferenceForm, ScalingOrbit, IntensionalCompletability}`,
`Cauchy/{DepthFloorDetOne, DepthOverflowDuality, DepthCeilingResidue}`, the C1′/C2/C3
conjectures (`G169`) and the discriminant trichotomy (`G170`).

## The question

Do the newly-merged G150 results (the meta-CD-tower's McKay `A–D–E` census, the
icosian/E₈ endpoint, seed-unit governance) help this branch's completability /
intensional-reduction / discriminant work — or break anything open?

## The breakthrough: the completability floor IS the E₈ endpoint (one `P`)

Both arcs, developed independently, land on the **same atomic matrix**
`P = [[2,1],[1,1]]` (trace `3 = NS`, det `1`, **disc `5 = NS+NT`**):

  - **completability bottom** — `DepthFloorDetOne`/`FloorReferenceForm`: `P` is the
    det-one *floor*, the trivially-free bottom of the rate-carrying stratification; its
    golden form `m²−mk−k²` (disc `+5`) is indefinite ⟹ a convergent line ⟹ completes;
  - **McKay top** — `MobiusPIcosian`: `P mod 5` is the order-`10` element of
    `SL(2,𝔽₅) ≅ 2I`, the **E₈** endpoint of the McKay `A–D–E` ladder
    (`10 = NT·(NS+NT)`).

So the **bottom** of the real-number completability tower and the **top** of the
exceptional-algebra ladder are the *same* `P`, met at the modulus `5 = NS+NT`.
`FiveFloorUnification.five_floor_unifies` bundles the two as one ∅-axiom statement.

This is breakthrough-flavoured because it closes a *loop*: the completability ladder has
no top (its ceiling is the diagonalisation residue, `DepthCeilingResidue`); its bottom
is this `5`-floor; and the `5`-floor is the McKay E₈ rung.  Bottom meets top — the same
self-covering "no exterior" (`05_no_exterior` §5.6: the same object recurring across
unrelated-looking domains is the operational content of having no outside).  It is a
*convergence*, not a derivation: neither arc reduces to the other; they independently
reach `P`/`disc 5`.

## Helps C2 (the rung floor): the discriminant gets a McKay home

`G170` refined C2 to "the rung floor is the discriminant of the reduced
cross-determinant," and `FloorReferenceForm`/`EisensteinSignature`/`ParabolicSignature`
gave the disc-sign trichotomy (line / cusp / curve).  The merge supplies the *McKay
home* of each discriminant, via `SeedUnitGovernance` (branch = odd torsion of the seed
unit group) and `MckayADECensus`:

  - **disc `−3`** (Eisenstein, `|μ| = 6 = NS·NT`) → `μ₆ = C₆` = the **A-family** (cyclic),
    the definite/curve rung;
  - **disc `+5`** (golden, `P`) → mod `5` the **E₈** rung (`2I`), the indefinite/line
    floor.

So the rung floor's discriminant is not just a sign — it names a McKay rung.  The
det-one floor sits at the `5 = NS+NT` discriminant, which is the E-family endpoint; the
Eisenstein definite reference sits at `−3`, the A-family.  C2's "algebraic coordinate of
the cut" is, concretely, *which McKay rung the reduced cross-determinant's quadratic form
belongs to*.

## Helps C3 (the residue): the cusp is the McKay/modular boundary

`G168`/`G170` tied C3 (the residue) to the parabolic cusp (disc `0`, the rational
direction) and the modular surface's one cusp.  The merge's McKay ladder makes the
elliptic points concrete (order-3 Eisenstein, order-2 Gaussian, the hyperbolic golden
`P`), so the trace trichotomy (|tr| `> 2` / `= 2` / `< 2`) that organises C3's
"line / cusp / curve" is now backed by named group rungs — the residue (cusp) is the
parabolic boundary between the hyperbolic floor (E₈-adjacent) and the elliptic
definite rungs.

## What it does NOT help (honest)

  - **C1′ / π** — untouched.  C1′ (a completing real = one with a rate-carrying
    re-presentation) and the π frontier are about *convergence rate / presentation*; the
    McKay/icosian structure is about the *unit-group / discriminant* of the floor, an
    orthogonal axis.  The merge does not produce a fast π series.
  - **The cross-presentation rung floor** (C2 over all presentations) — still open; the
    McKay home is for the floor's quadratic form, not a re-presentation invariant.

## Net

The merged G150 work delivers one genuine **breakthrough** for this thread — the
completability floor and the E₈ endpoint are one `P` (`five_floor_unifies`, ∅-axiom) —
and sharpens **C2** (the rung floor's discriminant names a McKay rung) and **C3** (the
cusp is the modular/McKay boundary).  It leaves **C1′/π** orthogonal.  The unification
is the operationally-meaningful one: the real-line's completability bottom and the
exceptional-algebra ceiling are the *same atomic object*, with `5 = NS+NT` the modulus
where they meet.
