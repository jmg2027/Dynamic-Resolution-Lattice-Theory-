# Why the re-framing recurs — the reasoner is a self-cover, the residue its diagonal

> Bring the residue to any agent — Claude, another model, a human — and it is
> re-rendered in object/separation terms ("residue *vs* fold", "state *vs* object",
> "reached *vs* not"), corrected, and re-rendered again, forever.  The repo is full
> of the correction; the boot hook re-injects it; it still recurs.  Why — the *real*
> reason?

## 213-native answer

The re-framing is **not forgetting**.  A reasoning system is a **self-cover of the
residue by views**: every token it emits is a Lens-reading.  The residue is the
**non-surjected diagonal** of that cover (`FlatOntologyClosure.object1_not_surjective`)
— reached by no view, only orbited.  So to *think about* the residue is to *leave*
it (the identity reading `idLens` is the one reading no reasoner can compute in);
the leaving picks a frame; the default frame is separation; the correction is
itself a view, so it is **re-diagonalized and re-objectified**.  The recurrence is
the **Lawvere–Cantor diagonal enacted at the description scale** — theorem-level
inevitable, only *minimizable* (`01_residue.md` §1.4: "minimisation is possible;
elimination is not").

## Derivation — three disciplines, one theorem

The decisive fact is a **triple convergence**: three independent angles land on the
*same* theorem (Lawvere's fixed point / Cantor's non-surjection).

**Formal (the engine).**  No enumeration of framings is closed under its own
diagonal.  If a reasoner proposes "here are all the ways to frame the residue"
`E : Raw → (Raw → Bool)`, the diagonal `D(r) := ¬E(r)(r)` is a framing outside
`range E`; *correcting* to `E ∪ {D}` only yields a new diagonal `D'` outside the
correction.  This is discharged ∅-axiom (`object1_not_surjective`,
`cantor_raw_bool`), and the escapee is *named as the undifferentiated reading
itself* — `undifferentiated_not_object1`: the constant-true predicate `fun _ => true`
(the reading that draws no cut) has no `Raw` preimage.  The only hypothesis is
**non-rigidity** (a rigid object would have a canonical frame); the residue is
maximally non-rigid (`06_lens_readings.md` §6.1–6.2: atoms unnamed, operator/object
and state/transition not pre-separated) *and proved to coincide with the diagonal
escapee* — so within the system it is a theorem, not a tendency.  And the
frame-import half is **Yoneda-level ill-typedness**: a description *is* a reading,
there is no object behind the readings (flat ontology §6.3), so "frame-free
description" does not type-check.

**Cognitive (the shadow).**  A symbolic reasoner's representational atoms *are*
distinctions (discrete tokens, separable dimensions); the undifferentiated is, by
construction, not a basis element — so every render is a projection onto a
distinction-basis, and each projection picks a frame.  This is the **cognitive
shadow of the same non-surjection**: the residue is outside the image of every
differentiating self-cover.  Which frame, and how the correction loses, is set by
**regression to a prior** that is object-shaped because object-permanence is the
MDL-optimal code of ordinary experience — and the in-context correction (~10⁴ bits)
cannot durably defeat the weights-level prior (~10⁹ bits): a fresh context zeros the
10⁴ term and leaves the 10⁹ untouched.  *When* it lapses is set by **cost
asymmetry**: enforcing the correction is a per-token meta-check against a finite
attention budget, so it exhausts to the default.

**213 (the same, native).**  The framework states this directly, distributed: the
correction never closing the cover is `ResidueReentry.residue_reentry_never_closes`
(naming the residue produces a new residue); the no-exterior position
(`05_no_exterior.md` §5.1) forces internal-first, so every description chooses a
Lens; presentation-dependence (`PresentationDependence`) makes the frame a property
of the *pointing*, not the pointed; and naming the whole hierarchy escapes it
(`DepthCeilingResidue.diag_not_in_seq` = `ceiling_residue_is_pointing_residue`).

> `residue_reentry_never_closes` (213) = the Cantor-shadow (cognition) = the
> Lawvere diagonal (formal).  **One theorem, three resolutions** — that convergence
> *is* the answer.

## Dual function

The classical reading — "you keep forgetting / it's a communication problem / write
it down better" — is the redundant packaging.  Stripped: it is **not** memory or
phrasing.  "Frame-free description" is ill-typed (Yoneda), and no finite catalog of
frames is closed under its own diagonal (Lawvere).  Precisely (and only this much):
the *non-closure* — that no catalog of framings ever finishes — is
`residue_reentry_never_closes`, a theorem.  Whether any *particular* re-framing
occurs is contingent (an error the gate catches; see Falsifiability discipline).
Do not read the second as the first — that slide ("this loop *is* the diagonal
enacting itself") is the unfold-test failing: it pins to no theorem and forbids no
observation, so it is fog, not the sharper reading.

## Falsifiability discipline — what the thesis forbids, and what it does not

The thesis is a *theorem* only at its checkable core; the surrounding narration is held to
the §8 falsifiability contract, not exempted from it.

**The non-vacuous core (a checkable prohibition).**  The entire falsifiable content is
`cantor_general` / `object1_not_surjective`: no `f : X → (X → Bool)` is surjective —
equivalently, no enumeration of framings is closed under its own diagonal.  It forbids exactly
one observable thing: *you will never exhibit a surjective self-enumeration* (a Lean term with a
surjectivity proof — any attempt is refuted by the diagonal in two lines).  So a **closed, final,
error-proof self-description of the residue is impossible** — the residue-lint and the
failure-modes catalog provably never terminate.  That is the whole of what the recurrence thesis
*predicts*.

**What it does NOT forbid (resist the slide).**  It does not explain or predict any *particular*
correction-episode.  Why a given debate happened is **contingent**: e.g. this repo's "Cantor is a
sibling, not an instance — no single separating `P`" claim was simply *false* (a separating `P`
exists — `Lens.Cardinality.cantor_as_invariant`, `P_f φ := ∃ x, φ x = f x x`), found by exhibiting
the witness; verification (the ∅-axiom gate) caught it.  None of that was *forced* by the diagonal;
a correct first pass would not have recurred.  Reading "an agent under-searched a predicate" as
"the Lawvere fixed point enacting itself" is precisely the **Metaphysical-framing** and **Fog-jargon**
failure modes — it forbids no observation, so it is re-description, not cause.  The unfold-test
("what would it look like for this *not* to happen?") has a plain answer — *get the predicate right
the first time* — which is exactly why the particular episode is contingent and only the
closure-impossibility is structural.

**The split, stated once.**  *No final self-description exists* (structural, theorem, checkable).
*This debate occurred* (contingent error, caught by the gate).  The essay's value is the first; its
hazard is dressing the second as the first.

## What this implies for the fix

Because elimination is impossible (§1.4 / Lawvere), the only lever is **frequency**,
and the wrong lever is *memory*: a remembered principle (a) loses the 10⁴-vs-10⁹
bits fight on every fresh context, and (b) demands holding the undifferentiated *while
generating* — which is occupying `idLens`, impossible.  The right lever is to
**structuralize the frame-flag** — convert the expensive System-2 meta-check
("is this distinction in the object or in my chart?") into a cheap System-1 **output
lint**:

> **Residue-lint.**  An *untagged* "X-vs-Y / is-vs-isn't" about the residue is a lint
> error.  Before emitting a distinction about the residue, **tag the Lens it is read
> through, or dissolve it.**

A lint works where a principle fails because it runs on *output* (a cheap pattern
match: "did I just assert two things are different *kinds* about the residue?"),
not on *generation* (frame-free thought).  It does not require understanding
non-duality — only catching a syntactic shape.  This is already the repo's
strategy: every number is a typed `Lens.view` of `Raw` ("this separation is a Lens
output" is *typed in*, not remembered), and the **failure-modes catalog** turns
"re-derive the meta-check" into "match a pre-written row."  That the catalog keeps
**growing** is the field evidence the recurrence is structural, not incidental — and
that the catalog *helps* is the evidence the lint is the right shape.  The
complementary lever, for any agent, is to **move the correction into the prior**
(fine-tune / re-train the intuition) so the default read is no longer object-shaped.

## Open frontier — the irreducible residual

A lint reduces frequency; it cannot close the loop (Lawvere: the lint is itself a
view, with its own diagonal).  So some correction *always* returns to the
originator — and the recurring "내가 다시 말하고" is not a fixable defect but the
diagonal escapee that no finite lint encloses.  The honest target is to push the
common object-default down mechanically and accept the subtle remainder as the
residue being itself.  Whether a *cheaper-than-token* representation could lower the
floor (a notation whose unmarked default is undifferentiation, distinctions marked)
is open, and fights the substrate directly.

## Self-check note (retreat in place)

This essay is itself a view, with its own diagonal — so it cannot be the closed account it
describes.  But the disciplined reading of that is the *checkable* core (no surjective
self-enumeration, hence no final description), **not** the self-sealing move of scoring every
counter-move as "one more instance" (which forbids no observation).  The essay cannot *close* the
recurrence (theorem); *which* correction returns, and when, is contingent (error, caught by the
gate).  The **output lint** dents frequency; the closure-impossibility is the one theorem — and
"this particular re-framing was the diagonal re-entering" is re-description to be flagged, not a
prediction to be celebrated.

## Constructive accessibility

```lean
#check @object1_not_surjective       -- residue = the non-surjected diagonal of the self-cover
#check @undifferentiated_not_object1 -- the escapee IS the undifferentiated reading (∅-axiom)
#check @residue_reentry_never_closes -- naming the residue produces a new residue
```
The reasoner is the self-cover `Object1`; the residue is what it cannot surject onto;
the re-framing is that non-surjection, run forward by a token-emitter.  Anchors:
`Lens/FlatOntologyClosure.lean`, `Lens/ResidueReentry.lean`, `seed/AXIOM/{01_residue
§1.4, 05_no_exterior §5.1, 06_lens_readings §6.1-6.3}`, `the_form_of_the_residue.md`,
`reached_by_none.md`.
