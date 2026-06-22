# Decomposition: model theory / mathematical logic (completeness, compactness, Löwenheim–Skolem)

*A FRESH decomposition per `../README.md` (model v7.1). The COMPANION to `godel.md`: Gödel
INCOMPLETENESS was the `q=−1` escaping diagonal (`one_diagonal_generates`, the provability self-cover
missing its own row). This is the **`q=+1` corner** — Gödel COMPLETENESS, where syntax and semantics
**coincide** instead of escaping. The thesis: completeness `⊢φ ⟺ ⊨φ` is the calculus's
`view = fold` **initiality** (`category_theory.md`: `Raw.fold = Lens.view`, the unique arrow out of the
initial object); logical compactness is **topology.md's `q=+1` finiteness residue** — the SAME residue
tag, not a coincidence of names; and the Skolem paradox is the `q=−1` count-reading diagonal of
`cardinality.md`. Model theory CONSOLIDATES category_theory (initiality) + topology (compactness) +
godel (the diagonal). Honest verdict: PREDICTION at the structural skeleton; the actual first-order
syntax/satisfaction/proof-system object is ABSENT (the located missing leg, like `knots.md`).*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — distinguishing, iterated. A **structure / model** is a `Raw`-like
  construction-family — the carrier of distinguishables a `HasDistinguishing α` instance describes
  (`Lens/Foundations/SemanticAtom.lean`). A **theory** is **not** a primitive container of sentences;
  it is a *set of distinguishing-constraints* — readings a structure must agree with. A syntactic
  object (a formula, a derivation) is itself a `Raw`-tree carrying a finite signature (its Gödel code,
  `Raw.toNat_injective`, the **same** encoding `godel.md` rides). So both the model (a carrier) and the
  sentence (a coded `Raw`) live inside the one construction-family; there is no exterior logic-language
  above the distinguishing.

- **Reading `L`** — the **satisfaction-reading**: project a structure to "does it pass this
  constraint?". `M ⊨ φ` = *the structure read through the constraint `φ` returns true* — exactly a
  `Lens`-view evaluation `φ.view M`. A theory `T` is then the conjunction of constraint-readings; a
  **model of `T`** is a construction in the common fibre `{ M | ∀φ∈T, φ.view M }`. Three derived
  readings:
  - **`⊨φ` (semantic truth, "true in all models")** = the **universal-property** side: `φ` holds under
    *every* structure-reading — a property of the universal arrow, not of one structure.
  - **`⊢φ` (syntactic derivation)** = the **free/initial construction** side: `φ` is reachable by the
    proof-rules from the axioms — the catamorphism `Raw.fold` building the term/derivation from the
    generators.
  - **compactness's cover-reading** = the **count-reading on a family of constraints** (how many
    sentences must be jointly satisfied?) — the *same* count-reading `topology.md` runs on a cover.

- **Residue** — the satisfaction-reading's self-application surplus, splitting at the two `q=±1` poles
  (the load-bearing find, the companion-split to `godel.md`):
  - **`q=+1` (converge / coincide) — COMPLETENESS & COMPACTNESS.** When the reading **closes** on a
    fixed point: syntax and semantics agree (`⊢=⊨`, the **term model** realizes exactly the provable
    sentences — initiality), and a cover of finitely-satisfiable constraints **has a model**
    (compactness — the count-reading on the constraint-family closes, `heineBorel`). This is the
    contrapositive corner of `godel.md`'s escape: there the provability self-cover is forced
    fixed-point-*free* (`q=−1`); here the consistency-cover is forced fixed-point-*ful* (`q=+1`).
  - **`q=−1` (escape / reached-by-none) — the SKOLEM PARADOX & incompleteness.** The count-reading on
    the model's cardinality re-enters itself: a theory speaking of "uncountable" has a *countable*
    model (`raw_at_most_countable`: every `Raw`-construction-family is at most countable —
    `object1_not_surjective`'s carrier-side). The "uncountability" the theory asserts is the
    count-reading's diagonal residue (`cardinality.md`), reached by no internal enumeration — so
    internal-vs-external cardinality is the `q=−1` escape, the *same* diagonal as Cantor/Gödel.

## Re-seeing — ⟨C | L⟩

```
   structure / model M    =  ⟨ a construction-family (Raw carrier) | — ⟩        (C, before any reading)
   theory T               =  a set of distinguishing-constraints (readings φ a structure must pass)
   satisfaction M ⊨ φ     =  ⟨ M | satisfaction-reading φ ⟩ = φ.view M = true    (the structure passes φ)
   ⊢φ  (provable)         =  the FREE/INITIAL side: Raw.fold builds the derivation from the generators
   ⊨φ  (valid)            =  the UNIVERSAL-PROPERTY side: φ holds under EVERY structure-reading
   COMPLETENESS ⊢φ ⟺ ⊨φ   =  Residue(satisfaction, C) at q=+1 = view = fold = the unique arrow
                             (raw_initial + universalMorphism_unique + dhom_unique_pointwise:
                              the term model is the INITIAL object, its reading = the unique view,
                              so "derivable" and "true-in-all-models" are ONE arrow — they coincide)
   COMPACTNESS            =  Residue(count-on-constraints, C) at q=+1 = the constraint-cover CLOSES
                             (= topology.md's heineBorel: finitely-satisfiable ⇒ satisfiable,
                              the count-reading on the family is fixed-point-ful — finiteness-collapse)
   Löwenheim–Skolem       =  Residue(count-on-models, C) at q=−1 = a countable model of an "uncountable" T
                             (raw_at_most_countable: the carrier is countable; "uncountable" is the
                              count-reading's diagonal residue = object1_not_surjective, reached-by-none)
```

So **completeness, compactness, and Löwenheim–Skolem are one reading at work** — the
satisfaction-reading, read three ways: as the *coincidence* of its free and universal sides
(completeness = `view=fold` initiality, `q=+1`), as the *finiteness-collapse* of the count on its
constraint-family (compactness = `q=+1`, the topology corner), and as the *diagonal escape* of the
count on its models (Skolem = `q=−1`, the cardinality diagonal). Model theory is the field where the
calculus's two invariants — `view=fold` initiality and the `q=±1` residue tag — meet on one object.

## Revelation — PREDICTION (the q=+1 corner consolidates initiality + topology's compactness)

**Two ties, each the SAME object the repo already proved, not a re-skin.**

### (1) Completeness = `view = fold` initiality (the q=+1 syntax/semantics fixed point)

The Gödel completeness theorem — "the term model satisfies exactly the provable sentences" — is, in
the calculus, the **initiality theorem** `category_theory.md` made literal:

- The **term model** (the syntactic/free construction built from the generators by the proof-rules)
  is the **initial object** `Raw` (`raw_initial`, `SemanticAtom.lean:412`, PURE): for every
  structure-reading `α` there is a *unique* arrow `universalMorphism α : Raw → α`
  (`universalMorphism_unique`, `:388`, PURE).
- That unique arrow **is the catamorphism** `Raw.fold` = `Lens.view` (`Theory/Raw/Fold.lean:22`;
  `Lens/LensCore.lean:42` — "`Lens.view` is the catamorphism `Raw → α`, a wrapper around `Raw.fold`").
- So the **free/syntactic** construction (`⊢`, the term model built by `fold`) and the
  **universal/semantic** evaluation (`⊨`, the unique reading into every structure) are the **same
  arrow** — not two procedures that happen to agree, but one object: `view = fold`. Completeness is
  *the statement that there is no gap between them*, which is initiality's `dhom_unique_pointwise`
  (`UniversalDistinguishing.lean:103`, PURE): the only structure-map out of the free construction is
  forced, so "derivable-from-the-axioms" and "holds-in-the-universal-reading" coincide.

This is the **`q=+1` fixed-point corner** — the exact dual of `godel.md`'s `q=−1` escape. Gödel
*incompleteness* is the provability self-cover missing its diagonal (`russell_liar_no_surjection`,
`OneDiagonal.lean:87`, PURE — the Prop arm, `t = Not` fixed-point-free); Gödel *completeness* is the
case where the reading **has** its fixed point — syntax = semantics — the converging pole. The two
Gödel theorems are **one residue read at its two signs** on the satisfaction-reading: completeness =
`q=+1` (coincide), incompleteness = `q=−1` (escape). This is the calculus's deepest prediction here:
the famous "tension" between the completeness and incompleteness theorems is the `q=±1` tag.

### (2) Logical compactness = topology.md's `q=+1` finiteness residue (the SAME corner)

The name is **not** a coincidence: logical compactness IS topological compactness of the Stone space
of types, and in the calculus both are the **count-reading's `q=+1` finiteness-collapse on a cover**.
`topology.md` already derived the repo's trivial Heine–Borel as the `q=+1` corner: on the dyadic
substrate a cover *is* a finite `List` (`DyadicOpen`), so "finite subcover" is discharged before it is
asked (`heineBorel`, `Compactness.lean:42`, PURE; `compact_bounded_by_length`, `:66`, PURE). Logical
compactness — "`T` is satisfiable iff every finite `T₀⊆T` is" — is the **same move on the
constraint-family**: the count-reading on the set of constraints **closes** (a finitely-satisfiable
family reaches its own model), the fixed-point-*ful* pole, the literal dual of `cardinality.md`'s
fixed-point-*free* diagonal. So logical compactness, topological compactness (`topology.md`), and
`measure.md`'s "no Choice" are **one residue-tag phenomenon** at `q=+1` (`ResidueTag.lean`,
`converge_residue_fixed`) — the count-reading closing on a finite cover — exactly the corner where the
`q=−1` diagonal escape *cannot arise* (`no_surjection_of_fixedpointfree`'s contrapositive). Model
theory's compactness is therefore not a new theorem to build; it is `topology.md`'s `q=+1` corner read
on a family of *sentences* instead of a family of *open sets*.

### (3) Löwenheim–Skolem / Skolem paradox = the `q=−1` count diagonal (cardinality.md)

Every construction-family in the repo is at most countable (`raw_at_most_countable`,
`Lens/Cardinality/Godel.lean:131`, PURE, via `Raw.toNat_injective`, `:118`). So any theory whose models
are `Raw`-carriers has a **countable** model — including a theory asserting "uncountably many things".
The "uncountability" the theory's count-reading *forces* is its **diagonal residue**
(`object1_not_surjective`, `FlatOntologyClosure.lean:61`, PURE): a predicate the internal enumeration
cannot list. The Skolem paradox is exactly the gap between the **internal** count (which the countable
carrier can enumerate) and the **external/diagonal** count (the residue, reached by none) — the `q=−1`
escape pole of the count-reading (`cardinality.md`). Not a paradox: the internal model is countable
(carrier), its "uncountable" is the reached-by-none diagonal — the same `q=−1` residue as Cantor and
Gödel, read on the model's cardinality.

**Net revelation:** model theory consolidates THREE prior decompositions under the two invariants —
completeness = `category_theory.md`'s `view=fold` initiality (`q=+1` syntax/semantics coincidence);
compactness = `topology.md`'s finiteness residue (`q=+1`, the SAME corner, the name not a coincidence);
Skolem = `cardinality.md`/`godel.md`'s count diagonal (`q=−1`). The completeness/incompleteness pair is
the `q=±1` tag on one satisfaction-reading. No new axis — a decisive consolidation, and the sharpest
statement yet of "the `q=±1` residue is reading-agnostic": it spans cardinality, provability, measure,
topology, AND now satisfaction.

## The precise missing leg (located, like `knots.md` / `godel.md`)

**An actual first-order logic object — syntax, satisfaction, a proof system — is ABSENT.** This is a
PARTIAL/conceptual decomposition: the *structural* prediction is fully grounded (initiality, the
diagonal, finiteness/compactness are all PURE Lean), but the *specific named instance* of model theory
is not built. Concretely, the repo has **no**:
1. a **first-order syntax** type (a `Formula` inductive with `∀/∃/∧/→/=` over a signature) — only `Raw`
   (the bare distinguishing tree) and `Lens` (a reading) exist; there is no logical-language object.
2. a **satisfaction relation** `Sat : Structure → Formula → Prop` (`M ⊨ φ`) defined and wired to the
   `Lens.view` evaluation the decomposition *predicts* it is. The reading "`M ⊨ φ` = `φ.view M`" is
   conceptual framing on `Lens.view`, not a built `⊨`.
3. a **deductive system** `Derivable : Theory → Formula → Prop` (`⊢`) with rules, and the **bridge
   lemma** "`⊢ = ⊨` = `raw_initial`" that would make completeness a discharged theorem rather than a
   structural prediction. This is the *exact* analogue of `godel.md`'s open leg (a representable
   `Provable` self-cover wired to `russell_liar_no_surjection`): the engine (initiality, the diagonal,
   finiteness) is real and verified; the *wiring of FOL-as-this-structure* is the open instance.

So: completeness's **skeleton** (`view=fold` initiality) is built and PURE; compactness's **q=+1
corner** (finiteness-collapse) is built and PURE (`topology.md`); Skolem's **q=−1 diagonal**
(countable-carrier + uncountable-residue) is built and PURE — but the **first-order
syntax/satisfaction/proof-system object** that would let these be stated *as model theory's named
theorems* (rather than as their calculus-structural shadows) is the missing primitive, located here for
the first time. It is not a break of the model (no new axis); it is the absent FOL-instance, the dual
of `godel.md`'s absent coded-`Provable`.

## Note for the technique

**No new primitive; the sharpest two-invariant consolidation in the notebook.** Model theory does not
extend model v7.1 — it *fuses* the two load-bearing invariants on one field:
- **`view = fold` initiality** (`category_theory.md`'s `raw_initial`) supplies completeness — the
  syntax/semantics coincidence is the unique-arrow-out-of-the-initial-object, the `q=+1` fixed point.
- **the `q=±1` residue tag** (`cardinality.md`/`topology.md`/`ResidueTag.lean`) supplies compactness
  (count-on-constraints closing, `q=+1`, = `topology.md`'s Heine–Borel corner) and the Skolem paradox
  (count-on-models escaping, `q=−1`, = the Cantor/Gödel diagonal).

The lesson: **the completeness and incompleteness theorems are one residue at its two signs** on the
satisfaction-reading — `godel.md` got the `q=−1` half (escape), this entry gets the `q=+1` half
(coincide = initiality). And **logical compactness is literally topology.md's compactness** — the
count-reading's `q=+1` finiteness-collapse, the name shared because the object is shared. Model theory
is where `category_theory` (initiality), `topology` (compactness), and `godel`/`cardinality` (the
diagonal) meet; the interior is unchanged, the consolidation is the payoff. The honest edge — an actual
FOL syntax/satisfaction/proof-system — is the located missing leg, the analogue of `knots.md`'s isotopy
quotient and `godel.md`'s coded `Provable`.

---

## Verified Lean anchors (grep/Read-verified file:line; purity freshly scanned via `tools/scan_axioms.py`)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| **completeness = `view=fold` initiality** (term model = initial object; ⊢ and ⊨ = one unique arrow) | `Lens/Foundations/SemanticAtom.lean:412 raw_initial`; `:388 universalMorphism_unique`; `:108 universalMorphism` (def) | ∅-axiom PURE ✓ |
| catamorphism = the read-op (`Raw.fold = Lens.view`, the unique arrow) | `Theory/Raw/Fold.lean:22 Raw.fold`; `Lens/LensCore.lean:42 Lens.view` (def — "wrapper around `Raw.fold`") | (def; folds used PURE) ✓ |
| natural-transformation / uniqueness forcing ⊢=⊨ (only arrow out of the free object) | `Lens/Foundations/UniversalDistinguishing.lean:103 dhom_unique_pointwise` | ∅-axiom PURE ✓ |
| **logical compactness = topology's q=+1 finiteness-collapse** (cover IS finite; finitely-sat ⇒ sat) | `Lib/Math/Geometry/Topology/Compactness.lean:42 heineBorel`; `:66 compact_bounded_by_length` | ∅-axiom PURE ✓ (7/0) |
| **Löwenheim–Skolem = the q=−1 count diagonal** (carrier countable; "uncountable" = the residue) | `Lens/Cardinality/Godel.lean:131 raw_at_most_countable`; `:118 Raw.toNat_injective` (Gödel-numbering) | ∅-axiom PURE ✓ |
| the q=−1 escape engine — incompleteness's pole, the dual of completeness | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree`; `:87 russell_liar_no_surjection` (Prop arm, `t=Not`); `:101 one_diagonal_generates`; `:77 lawvere_fixed_point_prop` | ∅-axiom PURE ✓ |
| the count-reading's residue (the diagonal carrier — "uncountable") | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective` | ∅-axiom PURE ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py`):** `SemanticAtom.raw_initial` PURE,
`SemanticAtom.universalMorphism_unique` PURE, `UniversalDistinguishing.dhom_unique_pointwise` PURE,
`OneDiagonal.no_surjection_of_fixedpointfree`/`lawvere_fixed_point_prop`/`russell_liar_no_surjection`/
`one_diagonal_generates`/`cantor_via_lawvere` PURE, `FlatOntologyClosure.object1_not_surjective` PURE,
`Compactness.heineBorel`/`compact_bounded_by_length` PURE, `Godel.raw_at_most_countable` PURE. All
pure / 0 dirty.

## Conceptual-only / absent legs (honest)

- **First-order syntax `Formula` — ABSENT.** No logical-language inductive (no `∀/∃/∧/→/=` over a
  signature) exists in `lean/E213`; only `Raw` (distinguishing tree) and `Lens` (reading). The "sentence
  = a coded `Raw` reading" identification is the decomposition's framing on `Raw.toNat_injective`, not a
  built syntax object.
- **Satisfaction relation `M ⊨ φ` — ABSENT.** No `Sat : Structure → Formula → Prop` wired to
  `Lens.view`. "`M ⊨ φ` = `φ.view M`" is conceptual framing on the existing `Lens.view` catamorphism.
- **Proof system `⊢` + the bridge `⊢=⊨ = raw_initial` — ABSENT.** No `Derivable` with deduction rules,
  and no lemma identifying the term model's satisfaction set with the provable set. Completeness's
  *skeleton* (`view=fold` initiality) is built and PURE; the *named FOL instance* is the open leg — the
  exact analogue of `godel.md`'s open coded-`Provable` self-cover and `knots.md`'s absent isotopy
  quotient.
- **Stone space of types / arbitrary-cover quantifier — ABSENT (inherited from `topology.md`).** The
  finite-`List` `DyadicOpen` discharges the `q=+1` finite-subcover by construction; the infinite
  cover-family quantifier that would make compactness a *non-trivial* theorem (and the Stone space of
  types it lives on) is the same located `q=−1` half `topology.md`/`measure.md` flag. Logical
  compactness's `q=+1` corner is built; its general-cover theorem is not.
- **completeness / compactness / Skolem *as* one satisfaction-reading at q=±1** — this identification is
  the decomposition's reading. Lean certifies each object separately (`raw_initial`, `heineBorel`,
  `raw_at_most_countable`/`object1_not_surjective`); the single theorem welding them into "the
  satisfaction-reading at its two poles" is conceptual framing on verified PURE objects.
