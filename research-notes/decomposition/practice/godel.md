# Decomposition: Gödel incompleteness / provability

*213-decomposition of "provable" and the Gödel sentence — LEVERAGE phase, per `../README.md`
(model v6) and the directly-related `cardinality.md` (the count-reading + its forced diagonal
residue = the one engine of the limitative theorems; Residue tagged `q = ±1`, escape pole
`q = −1` = the Lawvere fixed-point-free map).*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — distinguishing, iterated: a formal system's constructions are `Raw`s. A
  syntactic object (a formula, a derivation) is a tree built by the distinguishing act, and it
  carries a finite signature — its Gödel number — by the injective encoding
  `Raw.toNat : Raw → ℕ` (`Lens/Cardinality/Godel.lean` `Raw.toNat_injective`,
  `raw_at_most_countable`). The "system" is not a primitive container of sentences; it is the
  family of distinguishables the encoding tallies. No exterior: the candidate names (predicates,
  proofs) land back inside `Raw` (`ProofISA.isa_reflect = naming_is_internal`).
- **Reading `L`** — the **provability-reading**: project each construction `a` to its row, the
  predicate "what `a` proves / decides about each `x`" — a self-cover
  `f : A → (A → Bool)` (decidable arm) or `f : A → (A → Prop)` (the honest, undecidable arm).
  This is the *same self-cover shape* as `cardinality.md`'s count-reading `Object1`; the only
  change is the chosen feature — "is provable in the system" rather than "is one of these". A
  provability predicate is a reading of the system's own constructions, indexed by those same
  constructions (Gödel-coded), so `A = A`'s-predicates is **forced**, not chosen: the system can
  encode talk about itself (`Raw.toNat` injective ⇒ rows are addressable by their own codes).
- **Residue** — what the provability-reading **forces but cannot capture**: the diagonal
  `g a := t (f a a)` with `t` fixed-point-free. At `t = ¬` (Prop arm) this is the Gödel sentence
  `G ↔ ¬f a a` — "I am not provable here" — *no row*: outside the image of the provability cover.
  The residue is not a stronger axiom or a bigger system; it is the provability-cover's own forced
  non-surjection. This is **exactly** the `q = −1` escape pole of `cardinality.md`: the
  fixed-point-free modifier `¬` / `not` has no fixed point, so it oscillates *outside* every row
  (`OneDiagonal.no_surjection_of_fixedpointfree`).

## Re-seeing — ⟨C | L⟩

```
   "formal system"        =  ⟨ family of distinguishables (Gödel-coded Raws) | — ⟩
   "provable"             =  ⟨ system | provability-reading (the self-cover f) ⟩
   the Gödel sentence G   =  Residue(provability-reading, C),  q = −1   (the forced diagonal)
   Gödel's 1st theorem    =  P(⟨ provability self-cover f | provability-reading ⟩)
                          =  no f realises every predicate up to the value-equality
```

The provability-reading reads the system *as predicates on its own coded constructions* — each
construction `a` as a row `f a`. Cantor's decidable arm (`B = Bool`, `t = not`) gives "no
mechanical decider covers every Bool-predicate" (`OneDiagonal.cantor_via_lawvere`,
`Cantor.cantor_general`); the **Prop arm** (`t = Not`, `¬(P ↔ ¬P)` = the Liar) gives the genuinely
*undecidable* twin — `OneDiagonal.russell_liar_no_surjection` via `lawvere_fixed_point_prop`. Gödel
sits on the Prop arm: provability is a `→ Prop` self-cover, and the diagonal sentence "this is not
provable" is the Liar's `t = Not` fixed-point escape. The capstone
`OneDiagonal.one_diagonal_generates` names Cantor (Bool), Russell/Liar/**Tarski** (Prop), and the
residue's non-closure (Raw) as **three instances of the one construction `g a := t (f a a)`** —
and `ProofISA.isa_diagonalize` (= `cantor_general`) lists Gödel explicitly as one of the proofs
this single primitive compiles.

## LEVERAGE — does incompleteness fall out of the one diagonal residue?

**Genuine structural prediction, not collapse-only.** The calculus does not merely re-skin Gödel
in Lens-words; it *predicts* incompleteness from a property of the reading alone: **any reading
rich enough to encode its own diagonal must miss its diagonal element.** Two ingredients, both
already proven `∅`-axiom, force it:

1. **Self-encoding is available** — the system's constructions are addressable by their own codes:
   `Raw.toNat_injective` (`Lens/Cardinality/Godel.lean`) is the Gödel-numbering that lets a
   provability predicate be indexed by the very constructions it ranges over. This is *the*
   hypothesis ("rich enough to encode its own diagonal"), and it is a theorem here, not an
   assumption.
2. **The fixed-point-free modifier escapes** — `¬` has no fixed point up to `Iff`
   (`OneDiagonal.lawvere_fixed_point_prop` contrapositive in `russell_liar_no_surjection`), so the
   diagonal row cannot exist. `t = Not` is the `q = −1` (escape/oscillate-outside) pole; the
   *converging* `q = +1` pole (a modifier *with* a fixed point) would give **no** residue
   (`OneDiagonal.residue_needs_distinguishing`: on a non-distinguishing value space every modifier
   has a fixed point, so there is no diagonal escape — and `distinguishing_powers_residue`:
   `Bool`/`Prop` distinguish, so `¬`/`not` is fixed-point-free).

So incompleteness is **derived**: given (1) self-encoding + (2) a distinguishing value space (truth
vs falsity), the provability-reading's self-application *cannot* be surjective. Incompleteness is
not a pathology special to arithmetic — it is the `q = −1` residue of `cardinality.md` instantiated
on a different *reading* (provability) of the *same* construction (Gödel-coded `Raw`s). Same
`(C, L)`-shape, same residue, different feature projected — the precise pattern the calculus
predicts. The prediction even tells you *where incompleteness vanishes*: a system whose
value-space draws no distinction (no `¬` with escape) has no Gödel residue
(`residue_needs_distinguishing`), the exact dual of Cantor collapsing on a subsingleton.

**Honest coded-Gödel gap.** What is `∅`-axiom-closed is the *abstract* skeleton: the Lawvere/Liar
fixed-point escape on a `Raw`-self-cover (`russell_liar_no_surjection`, `one_diagonal_generates`),
plus the Gödel **numbering** itself (`Raw.toNat_injective`). What is **not** built is the
*coded-Gödel instance proper*: a Lean object `Provable : Raw → (Raw → Prop)` defined as
honest-provability in a specific deductive system, with the bridge lemma "the self-cover `f` =
that `Provable` predicate" and the representability of `Provable` inside the system (the Hilbert–
Bernays–Löb derivability conditions). The calculus *predicts* this instance lands at the
`russell_liar_no_surjection` diagonal, but `Lens/Cardinality/Godel.lean` currently delivers only
the numbering (Σ2), not a provability self-cover wired to it. `ProofISA.isa_diagonalize` *names*
Gödel as compiling to `DIAGONALIZE`, but that naming is the Church–Turing-flavoured **thesis** the
ProofISA docstring flags as a thesis, not a discharged proof. So: the engine and the coding are
real and verified; the *wiring of provability-as-this-self-cover* is the open instance.

## Note for the technique — does Gödel confirm the universal `q = −1` limitative engine?

Yes, and it sharpens the model. Gödel is the **same `(C, L) + residue` as `cardinality.md`, a
different reading**: `C` = Gödel-coded distinguishables, residue = the `q = −1` escape diagonal
`g a := t (f a a)`, and the *only* change from Cantor is the projected feature (`provable` vs
`how-many`) and the value-equality arm (`Iff`/Prop vs `Eq`/Bool). This is strong evidence that the
`q = −1` escape pole is the **universal limitative engine**: `one_diagonal_generates` already packs
Cantor + Russell/Liar/Tarski + the residue's non-closure into one term; Gödel is the provability-
reading entry of that same list (`isa_diagonalize` enumerates it), and Turing's halting problem is
its decidable-arm twin (the `Bool` cover). The decomposition adds nothing to the engine — it
*reuses* it — which is the calculus's deepest unity restated: the **`q = −1` residue is reading-
agnostic**. The shape-note for the model: incompleteness confirms that the residue's `q = ±1` tag
is the load-bearing invariant (not the carrier, not the feature). The honest residual — wiring a
representable `Provable` self-cover to `russell_liar_no_surjection` — is the analogue of
`cardinality.md`'s "reached-by-none, cover-dependent" ceiling: the abstract residue is proven, the
*specific named cover* is the work that stays.
