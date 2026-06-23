# R2 — orchestrator's contribution: the one wall appears on every axis

*Stated before agents F (genericity) and G (symmetry) report, to be tested against their findings.  Develops
R1's "one internal generative wall (the diagonal) + free parameters" by locating the diagonal on each axis.*

## Claim 1 — height-asymmetry IS the diagonal on the ordinal axis (Burali-Forti)

R1 found height-h (large cardinals) is free *asymmetrically* (always taller, never less — Gödel II), unlike
the symmetric selection-σ (forcing both ways).  **Why** asymmetric?  Because the height fiber (the ordinals /
the strength tower) **carries the diagonal at its top**: *there is no largest ordinal* — the ordinal sequence
escapes every bound, which is **Burali-Forti**, and Burali-Forti is a **diagonal** (no surjection onto the
ordinals; the class Ord is not a set, exactly `object1_not_surjective` on the height fiber).  So:

> The height parameter is one-way *because its fiber has the diagonal*.  "Always taller, no top" = the
> `q=−1` escape (`escape_residue_outside`) read on the ordinal axis; the would-be top (a completed tower) is
> reached-by-none (the diagonal).  Gödel II is the proof-theoretic shadow of Burali-Forti's diagonal.

## Claim 2 — the SAME one wall appears on every axis (the diagonal is axis-polymorphic)

The single wall (`one_diagonal_generates`, R1) is not one impossibility among many; it appears **once per
axis**, always the same Lawvere non-surjection, only the fiber changes:

| axis / fiber | the diagonal's name there |
|---|---|
| cardinality (power-set fiber) | **Cantor** (`cantor_via_lawvere`) |
| self-reference (Prop fiber) | **Russell / Liar / Tarski / Gödel** (`russell_liar_no_surjection`) |
| computation (program fiber) | **halting** (`computability_halting.md`) |
| **ordinal height (tower fiber)** | **Burali-Forti** — no top ordinal (Claim 1) |
| **σ-completeness (refinement fiber)** | **the generic** (Claim 3) |

This *extends* `one_diagonal_generates`: the wall is **axis-polymorphic** — `no_surjection_of_fixedpointfree`
instantiated at each fiber type.  R1's "exactly one wall" is sharpened: one wall, *appearing on every axis*,
which is why it organizes the whole structure.

## Claim 3 — "generic" = the height-completion of a selection-σ (= the diagonal on the σ-axis)

Agent F's question: what is a *generic* filter ("meets every dense set")?  My reading: density = "σ **decides
every** statement" = σ is **maximal/complete** = the **top of the refinement tower of partial σ's**.  So
genericity is a **height-h condition on a selection-σ** (the completion of the σ-tower), and over an infinite
poset that completion is **reached-by-none** — the diagonal again, on the σ-completeness axis.  Hence:

> "Generic" is neither a new free parameter (i) nor an independent wall (ii): it is the **height-completion
> of a selection-σ**, and like every height-completion it is **reached-by-none (the diagonal)**.  Forcing
> works precisely because you never *reach* the generic — you approach it through the σ-refinement tower
> (the modulus/presentation = the free approach), and the "generic filter over M" is the classical artifact
> of pretending an exterior `M` (§5.1: no exterior — so internally there is only the σ-tower and its
> reached-by-none completion).

## The unification this points to (for the R2 synthesis)

**One wall (the diagonal), axis-polymorphic, organizes everything.**  Free parameters are the *approaches*
to it on each axis: selection-σ = the symmetric (set-fiber, no internal diagonal) approach; height-h = the
asymmetric (tower-fiber, diagonal-at-top via Burali-Forti) approach; genericity = the height-completion of σ
(diagonal on the σ-axis).  The "symmetry law" (G): **a free parameter is asymmetric iff its fiber carries the
diagonal** — set-fibers symmetric (forcing), tower-fibers asymmetric (large cardinals / Burali-Forti).  This
would close R1's two-kinds split into a single criterion (fiber-has-diagonal?) driven by the one wall.

## Refutation conditions
- Claim 1 fails if height-asymmetry is provably *not* Burali-Forti (e.g. a height tower with a top that is
  still one-way — unlikely).
- Claim 3 fails if density does work that "height-completion of σ" misses (F should check).
- The symmetry law fails if a *set*-fiber (unordered) parameter is asymmetric, or a *tower*-fiber is
  symmetric (G should check).
