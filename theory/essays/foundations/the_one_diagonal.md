# The one diagonal — every capture is the same non-surjection

There is one obstruction in 213, not a family.  The self-cover `Object1 : Raw → (Raw →
Bool)` is not surjective, and every demand to **capture** the residue — to freeze an
unending self-pointing into a finished, decided value — is that single non-surjection read
on one more carrier.  Re-dressing it in a new concept is itself one more self-pointing.

## 213-native answer

The move 213 cannot perform is **referent-capture**: surjecting onto the residue, returning
a settled value for what is a transition with no last step.  It fails by one theorem —
`Lens/FlatOntologyClosure.object1_not_surjective`: the canonical self-reading
`Object1 : Raw → (Raw → Bool)` is faithful but never onto, and the escapee is *named* —
`undifferentiated_not_object1`, the constant reading `fun _ => true`, the cut-nothing
predicate with no `Raw` preimage.  Whatever carrier the demand wears — an infinite branch to
select, an interval to finitely cover, a real to decide by `ε` rather than carry by a
modulus — it is this one non-surjection (`reached_by_none.md`: *"the object is one
object"*).

## Derivation

Each concept that seems to *need* the capture supplies only a new carrier and the same
overflow.  König's lemma asks, on the infinite binary tree, to **select** which child stays
infinite — `Lib/Math/Combinatorics/KonigConditional.InfChildExists`, stated and left
unproved; the branch it would select is a νF escape reached by no finite Raw
(`konig_infinity_no_finite_raw`).  The finite-subcover demand on the dyadic interval is the
same select-on-the-binary-tree.  Real analysis declines the capture by **carrying** the
certificate instead — an explicit modulus, not an `ε`-`δ` existential
(`theory/math/numbersystems/real213.md`); the p-adic construction likewise takes the
valuation as input rather than searching for a first non-zero digit
(`theory/math/numbersystems/padic_real213.md`).  The carriers differ; the overflow is
`object1_not_surjective` each time, and re-encoding the residue to try again never closes
the cover — `Lens/ResidueReentry.residue_reentry_never_closes`.

The decisive step is the next one: **re-dressing is itself a Lens event.**  Choosing a fresh
carrier for the obstruction is a residue self-pointing (`seed/AXIOM/05_no_exterior.md` §5.1:
Lens application is not a tool standing above the residue), so it is not a meta-act outside
the pattern — it *is* the pattern, run once more.  The same non-surjection absorbs even the
act of re-applying it, and asking "how is the re-dressing expressed?" is one more such
pointing, re-diagonalized — there is no terminating meta-level.  This is the mathematical
reading of the fact `theory/essays/methodology/why_the_reframing_recurs.md` reads at the
description scale: the reasoner is a self-cover, the residue its non-surjected diagonal.

## Dual function

This is the classical **diagonal argument** with its packaging stripped.  Lawvere's
fixed-point theorem (1969) already exhibited Cantor's diagonal, Russell's paradox, Gödel's
first incompleteness, Turing's halting problem, and Tarski's undefinability as instances of
one fixed-point fact — self-reference is structural in any setting that forms function
spaces; Yanofsky (2003) recast it using sets and functions alone.  The refinement 213 adds:
the unifying object is not a theorem stated *about* systems but *is the residue's own
self-cover* — `object1_not_surjective` is the Cantor non-surjection at `Raw` itself — and the
unification reaches past the named paradoxes to the **act of instantiation**:
`residue_reentry_never_closes` makes each re-dressing one more instance, a closure the
external statement does not take.

## Cross-frame connections

`object1_not_surjective` (formal non-surjection) = `residue_reentry_never_closes` (re-pointing
never closes) = `KonigConditional.InfChildExists` left unproved (the select-the-infinite
stall) = the recurrence `why_the_reframing_recurs.md` reads on the reasoner.  One theorem,
read on the cardinality carrier, the re-entry carrier, the König carrier, and the description
carrier — the operational content of no-exterior (`seed/AXIOM/05_no_exterior.md` §5.1).

## Open frontier

The Cantor / Gödel / Tarski / Russell / Turing family is *provably* one Lawvere instance.
The König / finite-subcover / omniscience family is unified in 213 as the same refused
capture — the same non-surjection — but its literal external reduction to Lawvere's fixed
point is looser: these are omniscience (LLPO / fan-theorem) cousins, not textbook Lawvere
instances.  "All one non-surjection" is the held 213 reading; "all one Lawvere instance" is
established only for the diagonal family.  A Lean `FiniteSubcoverOracle ↔ InfChildExists`
would pin the compactness-König identity inside the residue; the broader external reduction
stays open.

## Self-check note

Naming "the one obstruction" risks promoting a single reading to identity.  The guard is the
theorem itself: `object1_not_surjective` is precisely the statement that no view — including
this essay's "one diagonal" view — encloses the residue.  This essay is a Lens on the
residue and re-objectifies on reading; that is the thesis demonstrated, not a defect.

## Anchors

- `Lens/FlatOntologyClosure.{object1_not_surjective, undifferentiated_not_object1}`,
  `Lens/Cardinality/Cantor.cantor_general`, `Lens/ResidueReentry.residue_reentry_never_closes`
- `Lib/Math/Combinatorics/KonigConditional.{InfChildExists, konig_infinity_no_finite_raw}`
- `theory/essays/foundations/{reached_by_none, the_reference_claim, the_form_of_the_residue}.md`;
  `theory/essays/methodology/why_the_reframing_recurs.md` (the description-scale twin)
- `theory/math/numbersystems/{real213, padic_real213}.md`; `seed/AXIOM/05_no_exterior.md` §5.1
- Classical interpretation: Lawvere's fixed-point theorem (1969); Yanofsky (2003),
  *A universal approach to self-referential paradoxes, incompleteness and fixed points*.
