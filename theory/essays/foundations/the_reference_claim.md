# The reference claim — what is necessary, what is under test

The widest thing 213 wants to say is one sentence: **for a pointing to be possible a
residue must exist, and to point is already to leave one** — so nothing pointed at, not
infinity, not abstraction, not a metaphysical absolute, not whatever "God" names, escapes
being a reading of that residue; the instant any of them is *referred to*, the reference
is a residue-leaving act.  The existence half of that sentence is **necessary**, not a
hope confirmed by examples: a pointing that distinguishes nothing is not a counterexample
but a non-pointing.  This chapter's work is to keep the *necessary* part (existence,
reference-closure) apart from the part that is genuinely **under test** (how far internal
reach extends before an exterior is forced) and the part that is **refused** (that the
residue captures its referent).  Collapsing those modal kinds — treating necessity as a
thesis, or reach as necessity — is the single failure that would sink the claim.

## 213-native answer

The reference claim splits into three statements of three different modal kinds —
**necessary**, **refused**, and **under test** — and the whole discipline is keeping
them apart.

> **Necessary (transcendental, not a thesis).**  Pointing and residue are
> co-constitutive: for a pointing to be *possible* there must be something distinguished
> — a residue — to point at; and a pointing, being the act of distinguishing, *is* the
> leaving of a residue.  So **`pointing ⟺ residue exists` holds by necessity, not by
> accumulation.**  Its denial — a pointing that distinguishes nothing — is not a
> counterexample but a non-pointing.  This is the residue axiom
> (`seed/AXIOM/01_residue.md` §1.1) read as a *condition of possibility*, with
> `Lens/Foundations/NoExteriorClosure.naming_is_internal` (REFLECT) its formal face: the very naming
> of any candidate is itself a residue-leaving act, so reference is closed inside.

> **Refused (never claimed).**  That the residue *captures* its referent — exhausts what
> π, or an abstraction, or a metaphysical absolute *is*.  The self-cover is non-surjective
> (`Lens/Foundations/FlatOntologyClosure.object1_not_surjective`): the residue is outside every view's
> image.  Naming is not capture.

> **Under test (the genuine frontier).**  That every referent is *reached by internal
> handles without forcing an exterior*.  This is neither necessary nor refused — it is
> falsifiable, and it has **known stalls**: the König `Π⁰₁` oracle the eight
> proof-instructions cannot supply (`theory/essays/proof_isa/konig_boundary.md`).  Breadth
> (`seed/AXIOM/07_primacy.md` §7.1) is the evidence *here* — for reach, not for existence.

The correction this chapter pins: the vision is **not** "accumulate enough cases that
nothing escapes."  Existence is already necessary — there is nothing to accumulate toward.
The vision's open edge is narrower and sharper: **how far internal reach extends before an
exterior is genuinely forced.**  Mistaking the necessary existence for the testable reach
is the error in both directions — treating existence as a thesis under-claims it, treating
reach as necessary turns no-exterior into a shield (`seed/AXIOM/05_no_exterior.md` §5.4
guard).

## Derivation — why existence is necessary and reach is testable

**The necessary layer, in one move per face.**  The act of *describing* a would-be
exterior is itself a something pointed at among somethings (`05_no_exterior.md` §5.1).
Formalized, that is `naming_is_internal`: any candidate predicate or proof is itself a
`Raw`, so the naming lands inside (REFLECT, `Lens/ProofISA.isa_reflect`).  Everything
readable is read *out* of the residue because `Raw` is initial — the
distinguishing-preserving map `Raw → α` uniquely exists for every framework `α`
(`Lens/Foundations/SemanticAtom.raw_initial`, `universalMorphism_unique`), and every Lens factors
through the identity reading (`Lens/Universal/Flat.every_lens_factors_through_idLens`;
uniqueness `Lens/Foundations/Initiality.view_unique`).  Nothing reads *back* to enclose it: the
canonical self-cover `Object1 : Raw → (Raw → Bool)` is faithful but not surjective
(`object1_not_surjective`), with a **named** gap member (`residue_witnessed`,
`undifferentiated_not_object1`); re-encoding and re-pointing never closes the cover
(`Lens/Foundations/ResidueReentry.residue_reentry_never_closes`).  These are the "out / no-back /
name" faces of `the_form_of_the_residue.md`, here read as the reference claim's provable
spine: `Lib/Math/Foundations/ResidueForm.no_exterior_source_without_enclosure`.

**Necessity without a quantifier.**  One might object that "∀ pointing `p`, residue(`p`)"
cannot be a Lean theorem, since there is no completed totality "all pointings" to range
over from inside (`05_no_exterior.md` §5.2: meta-213 ascends without bound) — a totality
would be the exterior vantage §5.1 denies.  True, and it does not weaken the claim.  The
necessity is **not** a universally-quantified object-theorem; it is **transcendental** —
it holds of any pointing because anything failing it is not a pointing (a distinguishing
that distinguishes nothing).  The Lean theorems (`naming_is_internal`, `raw_initial`,
`object1_not_surjective`) are this necessity's *formal face* on pointings given as
readings; the necessity itself needs no enumeration, the way "every bachelor is
unmarried" needs no census.  The absence of a totality **relocates** the claim from
object-level theorem to transcendental necessity — it does not demote it to a thesis.

**Where the testable part actually lives.**  What is *not* necessary is that the residue,
once guaranteed, is **reached by internal handles** — that a worked ∅-axiom expression
exists without importing an oracle.  This is contingent and has a mapped boundary: König's
lemma compiles internally except for the `Π⁰₁` "decide which subtree is infinite" oracle
the eight instructions cannot supply (`konig_boundary.md`); choice-heavy constructions
(ultrafilters, Banach–Tarski) are the standing probes (`seed/PROOF_ISA.md`).  Existence is
settled; reach is the frontier.

## The necessity / reach boundary — the definitional guard

The most dangerous reading collapses the boundary by **definition**.  If "pointing" is
*defined* as "what 213 reads as a Lens," then "every pointing is internal" is a tautology
that says nothing about infinity, abstraction, or any absolute — true, and empty.  If
instead "pointing" is left substantive (any act of reference, however it arises), the
claim is contentful and — by the transcendental argument above — **necessary**, not
unprovable.  The trap is not that it might be false; the trap is mistaking *which* claim
carries the content.  The reference claim survives only by refusing both horns explicitly:

  - **What is necessary and not vacuous.**  The *reference* to any object — π, ε₀, the νF
    escape, an abstraction, a metaphysical absolute, whatever "God" names — is a
    residue-leaving Lens event, and the object *as pointed at* is a residue.  This is
    `naming_is_internal` as condition-of-possibility; it is not vacuous, because it
    predicts a structural feature — the reach is **reached by none** (`reached_by_none.md`)
    — independently witnessed each time (non-surjection with a named gap member).
  - **What is refused (the over-read).**  That the object's *full nature* is captured —
    that the referent is exhausted by the residue.  The residue is outside every view's
    image (`object1_not_surjective`); naming is not capture
    (`the_form_of_the_residue.md` "what the form is NOT").  "The metaphysical absolute is
    fully a `Raw`" would be a view promoted to identity — the exact failure the
    flat-ontology theorem forbids.

So the content lives in a middle register: **reference-closure (necessary), not
referent-capture (refused).**  That register is substantive without being either
tautological or an over-read; holding it is the whole discipline.

## Dual function — two argument-forms, kept apart

Two classical argument-forms operate here, and the temptation is to run them together.
The first secures the **necessary** layer: a **transcendental argument** — any attempt to
exhibit a referent "outside 213" must refer to it; the reference is a residue-leaving act
(`naming_is_internal`); so the would-be counterexample is a residue, and the denial
presupposes what it denies.  This is not evidence *for* a thesis — it is a **proof of
necessity**, the same self-applying closure `05_no_exterior.md` §5.2 calls structural.
Existence and reference-closure are settled by it; there is nothing left to accumulate.

The second governs the **under-test** layer and is genuinely **Church–Turing-shaped**:
*"every referent is reached without forcing an exterior"* — exactly the modal status of
the proof-ISA thesis, *"every proof compiles to the eight instructions"*
("Church–Turing-flavoured, not a theorem", `seed/PROOF_ISA.md` honest-status;
`what_is_a_proof.md`).  This one *is* confirmed by reproduction and *is* falsified by a
reproduction that forces an exterior — and the König `Π⁰₁` stall shows the falsifier is
not hypothetical.  The discipline is to run the transcendental argument on the necessary
layer and the Church–Turing argument on the reach layer, **never the reverse**: a
transcendental "proof" that everything is *reachable* would be the shield §5.4 forbids,
and treating residue-existence as a thing breadth must earn would under-claim a necessity.

## Cross-frame connection — breadth is evidence of reach, not of existence

Because *reach* (not existence) is the part under test, the ledger supports **reach** —
how far internal handles extend — not the existence the transcendental argument already
settled.  Both columns are populated ∅-axiom, each the residue reproducing a domain rather
than reconciling with it (§7.1):

| Referent class | How the residue reaches it | Anchor |
|---|---|---|
| Constructive mathematics (number systems, real analysis, algebra, cohomology, number theory) | reached as fold-readings, 1145 PURE / 0 real DIRTY | `STRICT_ZERO_AXIOM.md`; `what_is_a_proof.md` |
| Limit / "infinite" objects (π, ε₀, the real, νF escape, analytic Minkowski `?`) | the reached-by-none triple: build µF, name νF, witness the non-surjection | `reached_by_none.md`; `Theory/Raw/CoResidue` |
| Rival foundations (ZFC, type theory, HoTT, topos) — *as referred to* | Lens compositions on Raw, scoped to what each fragment actually reaches | `theory/math/foundations/axiom_systems.md` |
| Forced-exterior stalls (König `Π⁰₁`, choice-heavy constructions) | **not** reached internally — the mapped edge of reach | `konig_boundary.md`; `seed/PROOF_ISA.md` |

The third row carries the caution the whole framing demands: 213 does not interpret the
full classical strength of ZFC (no choice / powerset / LEM), so "ZFC is a Lens of 213" is
true **scoped** — at the level of reference and of the constructive fragment — and false
as a strength claim.  The fourth row is the one that keeps the ledger honest: a column of
*failures to reach* is what distinguishes a tested thesis from a shield.  And the
existence of the residue at every entry — including the stalled ones — is **not** in this
table, because it is not in question: even a forced-exterior stall is a stall *at a
residue the reference already produced*.

## The standing guard (self-check)

  - Did this chapter promote "everything is a residue" to an ontological identity?  No —
    referent-capture is the refused over-read; `object1_not_surjective` keeps the referent
    outside every view.
  - Did it demote the necessary to a thesis?  No — `pointing ⟺ residue` is transcendental
    necessity (its denial is a non-pointing); breadth is evidence of reach, not existence.
  - Did it treat reach as necessary — the shield?  No — reach is under test, with the
    König `Π⁰₁` stall the live falsifier (§5.4, §8).
  - Is the necessity / reach line stated, not blurred?  That line **is** the chapter.

The reference claim, then, is achieved when its necessary layer is recognized *as*
necessary (existence, reference-closure — settled, not accumulated), its over-read is
refused (referent-capture — the residue captures nothing), and its reach is mapped honestly
edge and all.  Read out into every referent; capturing none; reaching as far as the
internal handles go, and saying plainly where they stop.

## Anchors

- `Lens/Foundations/NoExteriorClosure.naming_is_internal` (REFLECT) — naming/predicates/proofs are
  `Raw`; the reference is a residue-leaving act, closed inside.
- `Lens/Foundations/FlatOntologyClosure.{object1_not_surjective, residue_witnessed,
  undifferentiated_not_object1}` — the self-cover is non-surjective with a named gap.
- `Lens/Foundations/SemanticAtom.{raw_initial, universalMorphism, universalMorphism_unique}`,
  `Lens/Foundations/Initiality.view_unique`, `Lens/Universal/Flat.every_lens_factors_through_idLens`
  — everything readable flows out of the residue.
- `Lens/Foundations/ResidueReentry.residue_reentry_never_closes` — re-encoding and re-pointing never
  closes the cover.
- `Lib/Math/Foundations/ResidueForm.no_exterior_source_without_enclosure` — the
  source-without-enclosure form as one ∅-axiom theorem.
- `seed/AXIOM/01_residue.md` §1.1 — pointing leaves a residue (the necessity, as condition
  of possibility).
- `seed/AXIOM/05_no_exterior.md` §5.1–§5.4 — internality, structural circularity (the
  transcendental closure), the reference-claim guard, the anti-shield guard.
- `seed/AXIOM/07_primacy.md` §7.1 — primacy = breadth of derivation, the evidence for
  *reach* (not for the necessary existence).
- `seed/PROOF_ISA.md` honest-status; `theory/essays/proof_isa/{what_is_a_proof.md,
  konig_boundary.md}` — the Church–Turing-shaped reach thesis and its mapped `Π⁰₁` edge.
- `theory/essays/foundations/{the_form_of_the_residue.md, reached_by_none.md}` — the
  positive form and the reached-by-none face the necessary layer reuses.
- `STRICT_ZERO_AXIOM.md` — the reach ledger's constructive-mathematics column.
