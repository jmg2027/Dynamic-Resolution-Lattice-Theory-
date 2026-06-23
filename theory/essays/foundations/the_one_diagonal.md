# The one diagonal — every capture is the same non-surjection

There is one obstruction in 213, not a family.  The self-cover `Object1 : Raw → (Raw →
Bool)` is not surjective, and every demand to **capture** the residue — to freeze an
unending self-pointing into a finished, decided value — is that single non-surjection read
on one more carrier.  Re-dressing it in a new concept is itself one more self-pointing.

## 213-native answer

The move 213 cannot perform is **referent-capture**: surjecting onto the residue, returning
a settled value for what is a transition with no last step.  It fails by one theorem —
`Lens/Foundations/FlatOntologyClosure.object1_not_surjective`: the canonical self-reading
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
the cover — `Lens/Foundations/ResidueReentry.residue_reentry_never_closes`.

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

## The Lawvere fixed point, instantiated (no longer narrative)

The diagonal family is now *one Lean theorem with literal instances*, not a prose claim
(`Lens/Foundations/OneDiagonal.lean`, 7/7 PURE).  The single construction `g a := t (f a a)` is
`lawvere_fixed_point`: a point-surjective `f : A → (A → B)` forces every modifier `t : B → B`
to have a fixed point.  Its contrapositive `no_surjection_of_fixedpointfree` is the engine, and
the limitative theorems are *derived as instances of it*:

  - **Cantor** = `B = Bool`, `t = not` (`cantor_via_lawvere`, via `bnot_self_ne`);
  - **the residue** = `A = Raw` (`residue_is_lawvere_diagonal` *is* `object1_not_surjective` —
    the act of distinguishing's self-cover read through the same fixed point);
  - **Russell / Liar / Tarski undefinability** = the `Prop`/`Iff` arm `lawvere_fixed_point_prop`
    at `t = Not` (`russell_liar_no_surjection`, via the Liar `¬(P ↔ ¬P)`) — the undecidable twin
    of Cantor, ∅-axiom (no `propext`: the conclusion is `Iff`, not `Eq` on `Prop`).

`one_diagonal_generates` bundles the three.  So "the residue is the engine that generates the
limitative theorems" (`01_residue.md` §1.0.1) is *literal*: the remainder the distinguishing
always leaves (`distinguishing_always_leaves_residue`) is the non-surjected diagonal that forces
Cantor, Russell, the Liar, and Tarski — one fixed point, not four re-proofs.

## Open frontier

The **Gödel-numbered / halting** members remain narrative, not Lean instances: a literal
`lawvere_fixed_point` reduction of first-order provability-incompleteness or the halting problem
needs the encoding apparatus (a coded syntax / a model of computation) that is not yet built
∅-axiom.  The *abstract* fixed-point heart they share is now formal (`lawvere_fixed_point`); the
*coded* instances are the open extension.

The König / finite-subcover / omniscience family is unified in 213 as the same refused
capture — the same non-surjection — but its literal external reduction to Lawvere's fixed
point is looser: these are omniscience (LLPO / fan-theorem) cousins, not textbook Lawvere
instances.  "All one non-surjection" is the held 213 reading; "all one Lawvere instance" is
established only for the diagonal family.  The compactness-König identity is pinned inside
the residue: `KonigConditional.infChildExists_iff_finiteSubcover` (∅-axiom) shows the
selection form (`InfChildExists`) and the compactness/fan form (`FiniteSubcoverOracle`)
equivalent **exactly modulo one omniscience step** — selection ⇒ compactness is free
(contraposition), compactness ⇒ selection needs deciding the child-disjunction
(`¬¬(B∨C) → B∨C`, `LLPO`-flavoured).  So the local `WKL ⟺ Heine–Borel` identity is
reproduced on the residue carrier with the one ∞-decision named as the only gap; the
broader external reduction of the omniscience family to Lawvere stays open.

## Self-check note

Naming "the one obstruction" risks promoting a single reading to identity.  The guard is the
theorem itself: `object1_not_surjective` is precisely the statement that no view — including
this essay's "one diagonal" view — encloses the residue.  This essay is a Lens on the
residue and re-objectifies on reading; that is the thesis demonstrated, not a defect.

## Anchors

- `Lens/Foundations/OneDiagonal.{lawvere_fixed_point, no_surjection_of_fixedpointfree, cantor_via_lawvere,
  residue_is_lawvere_diagonal, lawvere_fixed_point_prop, russell_liar_no_surjection,
  one_diagonal_generates}` (the diagonal family as one fixed-point theorem, 7/7 PURE)
- `Lens/Foundations/FlatOntologyClosure.{object1_not_surjective, undifferentiated_not_object1,
  distinguishing_always_leaves_residue}`,
  `Lens/Cardinality/Cantor.cantor_general`, `Lens/Foundations/ResidueReentry.residue_reentry_never_closes`
- `Lib/Math/Combinatorics/KonigConditional.{InfChildExists, konig_infinity_no_finite_raw}`
- `theory/essays/foundations/{reached_by_none, the_reference_claim, the_form_of_the_residue}.md`;
  `theory/essays/methodology/why_the_reframing_recurs.md` (the description-scale twin)
- `theory/math/numbersystems/{real213, padic_real213}.md`; `seed/AXIOM/05_no_exterior.md` §5.1
- Classical interpretation: Lawvere's fixed-point theorem (1969); Yanofsky (2003),
  *A universal approach to self-referential paradoxes, incompleteness and fixed points*.
