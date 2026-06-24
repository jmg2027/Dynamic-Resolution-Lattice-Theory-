# The conserved residue — de-abstraction and totality are one instrument

This essay names what two separate lines of work turned out to be measuring: **one conserved
quantity, the residue**, approached from opposite directions.  Everything here is pinned to
∅-axiom theorems; nothing is asserted that is not exhibited.

## Two directions, one quantity

The session ran two programmes that looked unrelated:

- **De-abstraction** (downward).  Peel a result to strict 0-axiom and the abstraction it used —
  an axiom, a Mathlib asset — is exposed as a *frozen mechanism*; at the bottom sits the
  distinguishing at its three atom-readings (`de_abstraction_calculus.md`).
- **Totality-probing** (upward).  Take a claim that asserts *closure* — "every monotone map on a
  complete lattice has a fixed point", "every predicate is decided" — and ask whether it leaves a
  remainder (the falsification probe in the same file).

They converge on the same object.  The residue `object1_not_surjective` — the act of distinguishing's
self-cover `Object1 : Raw → (Raw → Bool)` is faithful but never total — is Cantor's gap
(`OneDiagonal.residue_is_lawvere_diagonal`), and the one diagonal generates Cantor, Russell, the
Liar, and Tarski as instances of a single fixed-point construction (`OneDiagonal.one_diagonal_
generates`).  De-abstraction finds this residue **frozen inside an axiom**; totality-probing finds it
**relocated by a closure-move**.  Same quantity, two faces.

## The sharpest form: the residue is *class*-dependent, not *carrier*-dependent

What makes this more than a metaphor is a verified theorem on a single carrier
(`Order/KnasterResidue.residue_is_class_dependent`, ∅-axiom).  On `Bool`:

- the **all-modifier** class contains a fixed-point-free map (`!`, `bnot_fpf`), so "every modifier
  has a fixed point" is **false** — a universal cover `A → (A → Bool)` is blocked: the Cantor/Lawvere
  residue;
- the **monotone** class does *not* contain `!` (`bnot_not_monotone`), so it has no fixed-point-free
  member and "every monotone endo has a fixed point" is **true** — residue-free.

Same carrier; the residue **toggles with the class**.  The dial is exactly *whether the map-class
admits a fixed-point-free member* (`fpf_member_refutes_totality` is the shared engine).  This unifies
the two faces of the limitative/totality literature:

| programme | class | fpf member? | outcome |
|---|---|---|---|
| Cantor / Russell / Tarski | all modifiers (incl. `Not`/`!`) | yes | residue forced |
| Knaster–Tarski (free side) | monotone, on a complete lattice | no | totality, residue-free |
| Knaster–Tarski (ℕ) | monotone, on incomplete ℕ | yes (`succ`) | residue (totality fails) |

"Reaches the power-object" — the criterion the falsification probe arrived at — is precisely "the
class admits a fixed-point-free member."  The full power-object `α → Bool` ranges over *all*
modifiers, so it always contains one (Cantor); restricting the class (to monotone) or completing the
carrier (so the fpf witness `succ` acquires its limit `∞`) removes the witness.

## Conservation: the residue relocates, it is never destroyed

A *totality-move* is how a closure-claim handles the gap.  Each relocates the residue — the full
catalogue is verified (`Order/{KnasterResidue,ResidueConservation}.lean`, all ∅-axiom):

- **Adjoin / complete** (Knaster–Tarski): force totality by assuming a completeness datum
  `glb : (α → Prop) → α` — a map *out of the power-object*.  The residue is in the hypothesis: drop
  it (work on ℕ) and `succ` exhibits it (`knaster_conclusion_false_on_nat`).  Completeness *is* the
  residue adjoined — the `∞` that is the lub of ℕ is the same reached-by-none limit the continuum's
  modulus points at (`Real213 … limit_unreached_but_decided`).
- **Restrict the class** (monotone): genuine totality, but only because the fpf witness was *excluded
  from view*, not removed — `!` still exists on `Bool`; the monotone class merely cannot see it
  (`residue_is_class_dependent`).
- **Stratify** (ascend a level): cover `α`'s residue at a strictly bigger type.  But `n < 2^n`
  (`nat_lt_two_pow`) — the power-object exceeds its carrier at *every* level — so the cover-ascent
  never reaches a residue-free top; the residue moves up one rung, never off the tower.  The
  never-closing tower *is* "infinity is the residue's shape."
- **Quotient** (identify the residue away): a **decidable** equivalence has a computable normal form —
  a total idempotent retraction (`parity_idempotent`, the minimal analogue of the free group's
  `proj`) — so its quotient is residue-free.  The residue relocates into *"does a computable normal
  form exist"*: decidable ⟹ free, **undecidable ⟹ residue** (the missing section, not exhibitable in
  ∅-axiom data — which is exactly its being a non-constructible residue).
- **Stay finitary / decidable**: genuinely residue-free (`Bool` endo by exhaustion; the free group's
  decidable normal form `proj`).  No Cantor gap when the carrier does not reach the power-object.

In every case the residue is **conserved**: present for every carrier (`cantor_via_lawvere {A}`),
toggled into or out of *a class's view*, but never made non-existent.  A move that "achieves closure"
has paid for it — by an assumed datum, a narrowed class, or a finitary restriction — and the payment
is the residue's new location.

## Why this matters: axioms *are* totality-claims

The unification cashes out a claim about the 0-axiom discipline itself.  A forbidden axiom is a
**totality-claim that freezes a residue** — but the three forbidden axioms sit at *different
epistemic depths*, and honesty requires distinguishing them:

- **excluded middle** (`∀ p, p ∨ ¬p`) totalises decision; its residue is **exhibited as a diagonal**
  — the Liar, the proposition that is its own negation, where decidability would need a fixed point
  of `Not`, which is fixed-point-free (`OneDiagonal.russell_liar_no_surjection`, ∅-axiom).  This case
  is *verified*.
- **propext** (`(a ↔ b) → a = b`) totalises the identification of equivalent propositions; its
  freeze is shown **non-load-bearing operationally** — every *Substitute* move in
  `de_abstraction_calculus.md` (`LawfulBEq → nat_beq_refl`, `Nat.lt_one_iff → lt_one_eq_zero`, …)
  replaces a propext-carrying stdlib lemma with a pure witness, exhibiting the constructible content
  the totality had frozen.  This case is *verified by the peel*, not by a single diagonal.
- **choice** totalises selection; its residue — the non-constructible witness — is a **meta-level
  non-derivability**, by its nature *not* exhibitable in ∅-axiom data (exactly the status of the
  undecidable quotient above).  This case is *argued, not exhibited*; the impossibility of depositing
  it is itself the point.

So the three are not uniformly "verified": EM is a deposited diagonal, propext's avoidability is a
deposited family of substitutions, and choice's residue is a principled meta-gap.  Stating them level
keeps the claim honest — the pattern (totality-claim freezes a residue) is real, but its *evidence*
ranges from exhibited theorem to in-principle non-exhibitable.

So peeling an axiom (de-abstraction) and probing a totality-theorem (Knaster–Tarski) are *the same
act*: locating the conserved residue the closure-claim froze or relocated.  The 0-axiom standard is
not hygiene — it is the instrument that keeps the residue visible, refusing the moves (adjoin a
classical axiom, assume completeness) that would push it out of view.  This is why the discipline
reveals more than an axiom-using development does: each axiom it refuses is a totality-claim, and
refusing it re-exposes the residue frozen inside.

## The frontier, made exact: Gödel-2 = the residue diagonal + the □-modality

The residue framework's *acknowledged* boundary is **Gödel-2 proper** (`T ⊬ Con(T)`): Cantor,
Russell, the Liar, Tarski *are* the one Lawvere diagonal, but Gödel-2 was kept a frontier — needing
the provability modality `□` with the derivability conditions D1–D3 / Löb, which the bare self-cover
has no analogue of ("form-agreement, not identity").  That boundary is now **exact and ∅-axiom**
(`Lib/Math/Logic/ProvabilityResidue.lean`), separating the two ingredients precisely:

- **Shared — the diagonal.**  The Gödel–Löb fixed point `C ↔ (□C → A)` *is* the residue's
  `lawvere_fixed_point_prop` at the modifier `t X := (□X → A)` (`loeb_fixed_point_is_lawvere`): the
  same construction as Cantor/Tarski, only the modifier differs.  The form-agreement is now exhibited,
  not asserted.
- **Extra — the modality.**  Löb (`loeb_abstract`) and Gödel-2
  (`goedel_two : ¬ Box False → ¬ Box (Box False → False)`) follow from `□` + **D1–D3** as the *only*
  additional hypotheses.

So the frontier is not a vague "needs a modality": it is **exactly the three derivability
conditions**, named and isolated.  This is itself an instance of the conservation thesis — Gödel-2's
content splits cleanly into the *shared residue diagonal* and the *extra D1–D3 the bare cover lacks*,
with the boundary drawn at a theorem rather than a hand-wave.

## Honest boundary

The residue's *existence* per carrier is Cantor's theorem — unbreakable, and to that extent the floor
is not falsifiable there.  The content is therefore not "a residue exists" but the **discriminator**:
which map-class sees it, and which *move* a given totality-claim used to relocate it.  That is
operational (`residue_is_class_dependent` decides it on `Bool` by a computation) and it is where the
real structure lives.  The catalogue of totality-moves — **adjoin, restrict, stratify, quotient** —
is now verified in full (`Order/{KnasterResidue,ResidueConservation}.lean`); the one genuinely open
edge is the *undecidable* quotient, whose residue is by its nature not exhibitable in ∅-axiom data
(an un-computable normal form *is* a non-constructible residue, `reached_by_none.md`).  This essay
names the invariant the moves conserve and pins the engine (`fpf_member_refutes_totality`), the
toggle (`residue_is_class_dependent`), and the four moves (`knaster_conclusion_false_on_nat`,
`residue_is_class_dependent`, `nat_lt_two_pow`, `parity_idempotent`) that make it a measurement
rather than a metaphor.
