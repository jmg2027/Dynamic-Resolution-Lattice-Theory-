# Decomposition: topos theory — the CAPSTONE world (a category of sheaves; Ω the subobject classifier; the Mitchell–Bénabou internal logic; geometric morphisms; "variable sets")

*A FRESH, CAPSTONE decomposition per `../README.md` (model v7.1). A topos consolidates four prior
entries at once: `category_theory.md` (213 IS category-theory-shaped, generated from the distinguishing —
`Raw` initial, `Lens.view = Raw.fold` the catamorphism, readings = morphisms), `sheaf_theory.md` (a
topos = a category of sheaves; a presheaf = a restriction-compatible reading; gluing = `q=+1` initiality),
`model_theory.md` (the internal logic = the satisfaction-reading; completeness = `view=fold`), and
`yoneda.md` (the self-describing capstone — an object IS its bundle of readings; Ω represents the
subobject functor). The thesis to TEST at the PREDICTION/REVELATION bar, not re-skin: a **topos** = the
calculus's `Raw`/`Lens` world of variable-sets; the **subobject classifier Ω** = the calculus's
distinguishing-target `Bool`, with `χ_A` the membership/indicator reading `Object1`; and — the deepest
leverage — **the internal logic is INTUITIONISTIC (Heyting, not Boolean), and THAT is why 213 forbids
Classical/propext/excluded-middle.** "213 is constructive" = "213 lives in the `q=+1` PURE corner of its
own topos, whose internal logic is Heyting" — a structural account of the repo's foundational ∅-axiom
stance, the same shape `measure.md` gave for "no Choice".*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the calculus's whole **world of variable-sets**: the construction-family the
  distinguishing generates (`Raw`, and any `DStr`-carrier — `UniversalDistinguishing.lean:40`), *together
  with* its readings-over-a-resolution. A topos's objects are not bare sets; they are **sets varying over
  a base** (sheaves / "variable sets"). In the calculus this is exactly `sheaf_theory.md`'s presheaf — a
  reading indexed over the resolution poset — and `OnLens.lean`'s iterated reading-of-readings
  `universalMorphismLevelTwo : Raw → Lens (Lens Bool)` (`:242`): the construction re-entering its own
  reading-type, no meta-hierarchy. `C` adds no new primitive over `category_theory.md`/`sheaf_theory.md`;
  it is the *closure of that world under its own structure* — finite limits (joint distinguishing =
  products), an initial/terminal object (`raw_initial`), and the power/predicate algebra.

- **Reading `L`** — the **classify-by-the-distinguishing-target reading**. A topos is the category whose
  defining extra structure is the **subobject classifier Ω** with its characteristic maps: every subobject
  `A' ↪ A` is the pullback of `true : 1 → Ω` along a *unique* `χ_{A'} : A → Ω`. In the calculus the
  distinguishing-target is **`Bool`**, and the characteristic/membership reading is literally built:
  - **Ω = `Bool`** — the two-valued distinguishing-target. `FlatOntology.lean` realises the whole
    flat-ontology table with `Bool` as the truth-value object: *"a type in the flat ontology is exactly a
    decidable predicate on `Raw^n` — a function to `Bool`"* (`Type213 := (Fin n → Raw) → Bool`,
    `FlatOntology.lean:60`). `Bool` is Ω: the codomain into which every distinction resolves.
  - **`χ_A` = the indicator reading `Object1`** — `Object1 : Raw → (Raw → Bool)`
    (`FlatOntology.lean:43`), `Object1 r = fun s => decide (s = r)`, is the characteristic map of the
    subobject `{r}`: the membership reading "is `s` in this subobject?" valued in Ω = `Bool`. Subobjects
    ARE decidable predicates `Raw → Bool` (`FlatOntology.lean` §9.3 rows 2–4: type/relation/function = a
    predicate); the classifier is the reading that sends a subobject to its membership function.
  - **The power object `Ω^A`** — the algebra of all such predicates `Raw → Bool`. The classifier
    self-cover `Object1 : Raw → (Raw → Bool)` (the embedding `A → Ω^A`) and its right-inverse
    `predicateToRaw : (Raw → Bool) → Raw` (`PredicateSelfEncoding.lean:71`) are the power-object adjunction
    one level apart — built and PURE.
  - **The internal logic = the connectives ON Ω.** The Mitchell–Bénabou language reads each formula as a
    map into Ω; the logical operations are operations on Ω. In the calculus the *`Bool`-valued / `decide`*
    operations are the constructive (Heyting) connectives — and the *`Prop`-valued classical* connectives
    are exactly where an axiom is paid (see Residue/Revelation).

- **Residue — the `q=±1` tag (`ResidueTag.lean:73`), at the topos's two faces.** Read the
  classify-reading's self-application; its surplus carries the tag, and the load-bearing find is that the
  **two faces of "the internal logic" split at `q=±1`, and the classical/Boolean face is the axiom-dirty
  one**:
  - **`q=+1` (converge / the PURE corner) — the Heyting/intuitionistic internal logic.** The `Bool`-valued,
    `decide`-based, finitely-definable predicate algebra round-trips (`predicate_self_encoding_closure`,
    `PredicateSelfEncoding.lean:91`) and is entirely PURE. Ω = `Bool` with the constructive connectives is
    the internal logic of the corner the repo lives in — the Heyting algebra of resolution-stable readings
    (`sheaf_theory.md`/`topology.md`'s `DyadicOpen` lattice). This is the converging/closure pole.
  - **`q=−1` (escape) — the residue Ω cannot enclose, AND the classical-logic cost.** Two escapes meet
    here. (i) The *power-object diagonal*: `Object1` is faithful but **not surjective**
    (`object1_not_surjective`, `FlatOntologyClosure.lean:61`) — the predicates outside its image are the
    Cantor-unpointable surplus (the residue itself; `self_covering_closure`, `:69`). (ii) The
    *classical-logic axiom cost*: realising the connectives **on `Prop`** (`∧`/`∨`/`↔`/truth as
    distinguishing — `propAsDistinguishingAnd`, `canonicalAndMap`/`canonicalOrMap`/`canonicalIffMap`,
    `SemanticAtom.lean:277,285,…`) is **DIRTY — it pulls `propext`** (scanned: 23 dirty in `SemanticAtom`,
    all `propext`). So the Boolean/two-valued *Prop* internal logic costs an axiom; only the constructive
    `Bool`/Heyting corner is PURE. The forbidding of classical logic is the `q=−1` boundary of the topos's
    own internal language.

## Re-seeing — ⟨C | L⟩

```
   a topos                =  ⟨ the Raw/Lens world of variable-sets | classify-by-the-distinguishing-target ⟩
   objects (variable sets/ =  constructions-varying-over-a-resolution  =  sheaf_theory.md's presheaves,
     sheaves)                  OnLens's Raw → Lens (Lens Bool) (reading-of-readings, no meta-hierarchy)
   morphisms              =  readings (Lens-arrows)  =  Lens.refines / DHom  (category_theory.md)
   finite limits          =  joint distinguishing (products = pair-distinguishing); equalizer = sheaf glue
   terminal / initial 1   =  Raw is initial (raw_initial); 1 → Ω picks `true`
   ★ subobject classifier =  Ω = Bool  (the distinguishing-target; FlatOntology.Type213 = Raw^n → Bool)
       Ω                       subobject A' ↪ A  =  a decidable predicate  =  χ : A → Bool
       χ_A                 =  the membership/indicator reading  Object1 : Raw → (Raw → Bool)
   power object Ω^A        =  the predicate algebra Raw → Bool; A → Ω^A = Object1 (faithful self-cover),
                              right-inverse predicateToRaw : (Raw → Bool) → Raw
   ★ internal logic       =  the connectives ON Ω = Bool  —  INTUITIONISTIC (Heyting):
       (Mitchell–Bénabou)      the decide/Bool corner is PURE (q=+1); the classical Prop corner is
                               DIRTY (propext) — WHY 213 forbids Classical/LEM
   Lawvere–Tierney topology=  the closure operator clo on Ω  =  galois.md's clo = G∘F (idempotent,
       j : Ω → Ω               clo_idempotent) — the modality "locally true" = resolution closure
   geometric morphism     =  a reading-between-worlds (f^* ⊣ f_*)  =  galois.md's adjoint pair gc (F ⊣ G)
   a point of the topos   =  a reading from the one-point world  =  universalMorphism α : Raw → α
   RESIDUE                =  q=+1 Heyting PURE corner / q=−1 Ω-diagonal + classical-logic axiom cost
```

So **the topos, Ω, the internal logic, Lawvere–Tierney, and geometric morphisms are ONE reading at
work** — classify-by-the-distinguishing-target — over the `Raw`/`Lens` variable-set world, with its
`q=+1` Heyting corner PURE and its `q=−1` corner being both the Cantor power-object residue and the
propext cost of going classical.

## LEVERAGE — does a topos consolidate category_theory + sheaf + model_theory's logic + the constructive discipline?

**Verdict: PREDICTION + PARTIAL — the sharpest *foundational* leverage in the notebook: the topos's
intuitionistic internal logic is a STRUCTURAL EXPLANATION of 213's own ∅-axiom/no-Classical discipline
(the `measure.md`-grade payoff), cashed at the Ω = `Bool` / `χ = Object1` / `clo` = Lawvere–Tierney /
geometric-morphism = adjoint-pair level (all PURE); PARTIAL because no *named* topos / subobject-classifier
Ω / Mitchell–Bénabou-language / geometric-morphism OBJECT exists — the precise missing leg, located like
`knots.md`/`sheaf_theory.md`.** Leg by leg, honest.

**(1) A topos = the calculus's `Raw`/`Lens` variable-set world — built as the category, not as a named
`Topos`.** `category_theory.md` proved (PURE) that readings form a category: `Raw` is the initial object
(`raw_initial`, `SemanticAtom.lean:412`), `universalMorphism`/`Raw.fold` is the catamorphism = the unique
arrow out of it (`:108`, `Lens.view` `LensCore.lean:42`), readings are the morphisms (`Lens.refines`,
groupoid `LensIso`). `sheaf_theory.md` added the variable-set layer: presheaves = readings over the
resolution poset (the structure built, the assignment-object conceptual). `OnLens.lean:242` builds the
"variable set" literally — `Raw → Lens (Lens Bool)`, the construction varying over its own reading-type,
"no meta-hierarchy". This IS a topos's category of variable-sets; what is absent is the *packaged* claim
"this category is a topos" (finite limits + Ω + power objects as one bundled theorem).

**(2) ★ Ω = the distinguishing-target `Bool`; `χ_A` = the indicator reading `Object1` — BUILT and PURE,
the load-bearing collapse.** This is the entry's strongest grounded leg and is *not* conceptual. The
subobject classifier's defining role — every subobject is the pullback of `true` along a unique
characteristic map `χ : A → Ω` — is the calculus's flat ontology verbatim: `FlatOntology.lean` realises
*type / subset / relation / function* uniformly as **decidable predicates valued in `Bool`**
(`Type213 := (Fin n → Raw) → Bool`, `:60`), and `Object1 : Raw → (Raw → Bool)` (`:43`,
`Object1 r = fun s => decide (s = r)`) is the characteristic map of the singleton subobject `{r}`. The
power object `Ω^A` is the predicate algebra `Raw → Bool`; the embedding `A → Ω^A` is `Object1` (faithful,
`object1_injective`, `FlatOntologyClosure.lean:47`) and its definable right-inverse is
`predicateToRaw : (Raw → Bool) → Raw` (`PredicateSelfEncoding.lean:71`, round-trip
`predicate_self_encoding_closure`, `:91`). So **Ω, `χ`, and the power object are present and PURE as
`Bool`, `Object1`, and the predicate algebra** — the named categorical `Ω`/`SubobjectClassifier`/`PowerObject`
*types* are the only absence. The `DStr` schema is even described in-repo as "the distinguishing as a
*classifier*" (`Lens/INDEX.md:52`, `Foundations/INDEX.md:32`).

**(3) ★★ The internal logic is INTUITIONISTIC — and that is WHY 213 forbids Classical/propext (the
deepest leverage, `measure.md`-grade).** This is the entry's revelation and is *grounded by a purity
scan*, not asserted. A topos's internal (Mitchell–Bénabou) logic is the algebra of maps into Ω, and it is
**Heyting, not Boolean** — constructive, no excluded middle in general. The calculus exhibits exactly this
split at the axiom level:
- The **`Bool`-valued / `decide`-based** connectives — the constructive Heyting corner — are **PURE**:
  `Object1` (`decide (s = r)`), the whole `FlatOntology` predicate algebra, `predicateToRaw`, the
  `Bool`-combine `OnLens` morphisms (`universalMorphismLevelTwo`, `:242`) are ∅-axiom (scanned).
- The **`Prop`-valued / classical** connectives — Boolean two-valued logic — are **DIRTY, pulling
  `propext`**: `propAsDistinguishingAnd`/`canonicalAndMap` (`SemanticAtom.lean:277,285`),
  `…Or…`/`…Iff…`/`canonicalTruthMap` — the scan reports **23 dirty in `SemanticAtom`, every one
  `[propext]`**. `propext` (propositional extensionality, the classical collapse of `Prop` to a Boolean
  truth-value object) is exactly the axiom 213's discipline forbids (CLAUDE.md ∅-axiom standard:
  "No `propext`, `Quot.sound`, `Classical.choice`…").

So the repo's foundational stance — **"213 forbids Classical / propext / excluded middle"** — is, read
through this decomposition, **the statement "213 lives in the `q=+1` PURE corner of its own topos, whose
internal logic is intuitionistic (Heyting), and the Boolean/classical corner is exactly the axiom-dirty
one."** The ∅-axiom discipline is not an external rule imposed on the theory; it is the *internal logic of
the topos the calculus is*. This is the structural account `measure.md` gave for "no Choice" (the `q=−1`
escape of an uncountable weight-reading), now given for "no Classical/LEM" (the `q=−1` propext cost of the
Boolean internal logic). The same `ResidueTag` (`:73`, `escape_residue_outside` `:133` / `converge_residue_fixed`
`:160`, both PURE) that unites Cantor/Gödel/measure (escape) with φ/Gaussian/ODE (converge) now also tags
constructive-Heyting (`q=+1`, PURE) vs classical-Boolean (`q=−1`, propext).

**(4) Lawvere–Tierney topology `j : Ω → Ω` = `galois.md`'s closure operator `clo` — BUILT and PURE.** A
Lawvere–Tierney topology is an idempotent inflationary modality on Ω selecting "locally true"
propositions; the sheaves are the `j`-separated/closed objects. This is exactly `galois.md`/`adjunction.md`'s
**closure monad** `clo = G∘F` (`GaloisConnection.lean:104`) with `clo_extensive` (inflationary/unit, `:107`),
`clo_idempotent` (`T²=T`, `:126`), arising from the adjoint pair `gc` (`gc_unit`/`gc_counit`/`gc_fgf`/`gc_gfg`,
`:41,49,79,91`) — all PURE. The "locally true" modality = the **resolution closure**: a proposition is
`j`-true iff it holds resolution-stably, the `q=+1` idempotent pole (`sheaf_theory.md`'s gluing corner).
`clo` is the Lawvere–Tierney topology; the named `j : Ω → Ω` typing on `Bool` is the only absence.

**(5) Geometric morphisms / points = readings-between-worlds = the adjoint pair / `universalMorphism`.** A
geometric morphism `f : E → F` is an adjoint pair `f^* ⊣ f_*` with `f^*` left-exact — a structure-preserving
reading between two topoi. This is the calculus's adjoint reading-pair `F ⊣ G` (`gc`, `GaloisConnection.lean`,
PURE) and, schematically, a `DHom` between two `DStr`-worlds (`UniversalDistinguishing.lean:85`,
structure-preserving carrier-map = a functor between construction-families). A **point** of a topos (a
geometric morphism from the one-point topos) = a reading from the terminal/initial world = `universalMorphism α
: Raw → α` (`SemanticAtom.lean:108`, the unique arrow), `model_theory.md`'s "a model is a reading into a
structure". So geometric morphisms = `category_theory.md`'s functors / adjoint pairs; the named
`GeometricMorphism` object with the left-exactness condition is conceptual.

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, freshly scanned PURE):* (a) the **variable-set category** — `raw_initial`
  (`SemanticAtom.lean:412`), `universalMorphism`/`_unique` (`:108,388`), `dhom_unique_pointwise`
  (`UniversalDistinguishing.lean:103`), `Lens.view`/`Raw.fold` (`LensCore.lean:42`), `universalMorphismLevelTwo`
  (`OnLens.lean:242`); (b) **Ω = `Bool` + `χ` = `Object1` + power object** — `Object1`/`Object1_self`/`Type213`
  (`FlatOntology.lean:43,46,60`), `object1_injective`/`object1_not_surjective`/`self_covering_closure`
  (`FlatOntologyClosure.lean:47,61,69`), `predicateToRaw`/`predicate_self_encoding_closure`
  (`PredicateSelfEncoding.lean:71,91`); (c) **the intuitionistic-vs-classical axiom split** — `Object1`
  (`decide`) PURE vs `propAsDistinguishingAnd`/`canonicalAndMap`/`canonicalOrMap`/`canonicalIffMap`/
  `canonicalTruthMap` DIRTY `[propext]` (`SemanticAtom.lean:277,285,299…`; scan: 43 pure / 23 dirty);
  (d) **Lawvere–Tierney = `clo`** — `clo`/`clo_extensive`/`clo_idempotent`/`gc_*` (`GaloisConnection.lean:104,107,126,41,49,79,91`);
  (e) **the `q=±1` tag** — `ResidueTag`/`escape_residue_outside`/`converge_residue_fixed`/`residue_tag_two_poles`
  (`ResidueTag.lean:73,133,160,228`).
- *Conceptual-only / the precise missing leg:* **a NAMED topos / subobject-classifier Ω / Mitchell–Bénabou
  language / geometric-morphism object is ABSENT.** Grep over `lean/E213` for
  `topos`/`Topos`/`classifier`/`Subobject`/`subobject`/`powerObject`/`PowerObject`/`geometricMorphism`/
  `LawvereTierney`/`Heyting`/`TruthValue` returns **zero categorical Lean declarations** (the only `Omega`
  hits are physics namespaces — `ZOmega`, `OmegaH2Trace` — and the `ω` ordinal; "classifier" appears only in
  prose docstrings naming the `DStr` schema). There is **no** `Topos` structure bundling
  finite-limits + Ω + power-objects; **no** `Ω`/`SubobjectClassifier` typed on `Bool` with the
  pullback-of-`true` universal property; **no** `InternalLanguage`/Mitchell–Bénabou translation; **no**
  `GeometricMorphism`/`LawvereTierneyTopology` typed on `Bool`. This is the SAME shape as
  `sheaf_theory.md`'s missing presheaf-object and `knots.md`'s missing isotopy quotient: the *truth-value
  target* (`Bool`), the *characteristic reading* (`Object1`), the *power-object round-trip*
  (`predicateToRaw`), the *closure modality* (`clo`), the *adjoint geometric reading* (`gc`), and the
  *intuitionistic/classical axiom split* (the propext scan) are each built and PURE; the **bundled `Topos`
  with its named Ω and internal language** is the open leg.

So: **PREDICTION on the consolidation (a topos = the `Raw`/`Lens` variable-set world; Ω = `Bool`; `χ` =
`Object1`; the internal logic is intuitionistic = WHY 213 forbids Classical/propext; Lawvere–Tierney =
`clo`; geometric morphisms = adjoint readings), cashed at the truth-value / classifier / closure /
adjoint / axiom-split level (all PURE); PARTIAL because the named topos / Ω / internal-language /
geometric-morphism OBJECTS are absent — the located open legs, not hand-waves.**

## REVELATION (the constructive discipline EXPLAINED: 213's ∅-axiom stance = its topos's intuitionistic internal logic)

**Collapse + structural-account — the topos, Ω, the internal logic, Lawvere–Tierney, and geometric
morphisms are ONE classify-reading over the calculus's variable-set world, AND that world's internal logic
being Heyting (not Boolean) is a derived explanation of the repo's own no-Classical/∅-axiom discipline.**
The single forcing sentence, read at both poles of the `q=±1` tag on the classify-by-Ω reading:

- **`q=+1` (the PURE / converging corner = the Heyting internal logic = where 213 lives).** Ω = `Bool`,
  the distinguishing-target; subobjects = decidable predicates `Raw → Bool`; `χ_A = Object1` the membership
  reading (`object1_injective`, faithful); the connectives are the `decide`/`Bool` operations — the
  **intuitionistic Heyting algebra of resolution-stable readings**, all ∅-axiom. Lawvere–Tierney = `clo`
  (`clo_idempotent`, the resolution-closure modality picking "locally true"), the `q=+1` converging pole.
  Gluing/initiality (`dhom_unique_pointwise`, `raw_initial`) settles the sheaf condition. **This is the
  corner the repo's ∅-axiom discipline IS.**
- **`q=−1` (the escape corner = both the power-object residue AND the classical-logic cost).** Two escapes
  coincide. The power-object self-cover `Object1 : Raw → (Raw → Bool)` is faithful but **not total**
  (`object1_not_surjective`, the Cantor-unpointable predicates = the residue, `self_covering_closure`).
  And going **Boolean/classical** — the `Prop`-valued connectives `propAsDistinguishingAnd`/`canonicalAndMap`/…
  — **costs `propext`** (DIRTY, the scan: 23 propext-dirty in `SemanticAtom`). So the Boolean two-valued
  internal logic is the `q=−1` axiom-escape; only the constructive Heyting `Bool` corner is PURE.

This passes the re-skin guard at the prediction bar: it does not re-describe a topos — it **derives 213's
foundational stance from the topos structure.** "Why does 213 forbid Classical/propext/excluded-middle?"
gets a structural answer, not a methodological fiat: **because 213 is the `q=+1` PURE corner of its own
topos, and the internal logic of a topos is intuitionistic (Heyting); the Boolean/classical internal logic
is provably the propext-dirty `q=−1` corner.** This is the `measure.md`-grade leverage — there "no Choice"
became the `q=−1` escape of an uncountable weight-reading; here "no Classical/LEM" becomes the `q=−1`
propext cost of the Boolean internal logic. The topos is the field that **unifies** the calculus's whole
spine: `category_theory.md` (the variable-set category — initial object, catamorphism, morphisms),
`sheaf_theory.md` (a topos = sheaves; gluing = `q=+1` initiality), `model_theory.md` (the internal logic =
the satisfaction-reading; completeness = `view=fold`), `yoneda.md` (Ω represents the subobject functor; an
object = its bundle of readings), and `galois.md`/`adjunction.md` (Lawvere–Tierney = `clo`; geometric
morphisms = adjoint pairs) — and adds the one new foundational reading: **the repo's constructivity is its
topos's intuitionistic internal logic.** The deepest line: **the ∅-axiom standard (no propext) and the
intuitionistic internal logic are one statement** — the PURE/DIRTY boundary in `SemanticAtom`'s
`Bool`-vs-`Prop` connectives IS the Heyting-vs-Boolean boundary of the internal language.

## Note for the technique

**No new axis; the deepest *foundational* consolidation — the calculus's own ∅-axiom discipline is now a
derived theorem-shape, not a posited rule.** Topos theory does not extend model v7.1; it fuses four prior
fusions and turns the repo's foundational stance into a `q=±1` reading:
- the **variable-set category** (`category_theory.md`/`sheaf_theory.md`) supplies the topos's objects and
  morphisms (`raw_initial`, readings, `OnLens`'s reading-of-readings);
- **Ω = the distinguishing-target `Bool` + `χ = Object1`** (`FlatOntology`, `yoneda.md`'s representing
  object) supplies the subobject classifier and power object;
- **`clo`** (`galois.md`/`adjunction.md`) supplies Lawvere–Tierney; the **adjoint pair `gc`** supplies
  geometric morphisms; `universalMorphism` supplies the points;
- the **`Bool`-PURE vs `Prop`-propext-DIRTY split** (the `SemanticAtom` scan) supplies the internal logic's
  intuitionistic character — and *therewith* the structural explanation of 213's no-Classical discipline.

The lesson for the model: **the constructive/∅-axiom discipline is the `q=+1` Heyting corner of the
calculus's own topos** — the same `ResidueTag` that tags Cantor/Gödel/measure (escape) vs φ/Gaussian/ODE
(converge) now tags classical-Boolean-logic (`q=−1`, propext-dirty) vs constructive-Heyting-logic (`q=+1`,
PURE). And the topos being the calculus's own world confirms `yoneda.md`'s capstone once more: an object
IS its bundle of readings (the Yoneda principle), Ω = `Bool` is the target every reading resolves into, and
the subobject classifier = the reading-that-classifies-readings (`Object1`, the self-cover). The one
genuine absence — the named topos / Ω / Mitchell–Bénabou / geometric-morphism object — is located
precisely: the categorical twin of `sheaf_theory.md`'s missing presheaf object. **EXTEND by consolidation;
no new axis; interior model v7.1 holds; the foundational payoff is the strongest leg.**

---

## Verified Lean anchors (file:line — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| topos objects = variable-set category (initial object + catamorphism = read-op) | `Lens/Foundations/SemanticAtom.lean:412 raw_initial`, `:108 universalMorphism`, `:388 universalMorphism_unique`; `Theory/Raw/Fold.lean Raw.fold`; `Lens/LensCore.lean:42 Lens.view` | ∅-axiom PURE ✓ (scanned) |
| variable set / reading-of-readings (no meta-hierarchy) | `Lens/Compose/OnLens.lean:242 universalMorphismLevelTwo : Raw → Lens (Lens Bool)`, `:247 …LevelThree` | ∅-axiom PURE ✓ |
| functor/nat-trans schema; gluing = unique amalgamation (sheaf side) | `Lens/Foundations/UniversalDistinguishing.lean:40 DStr`, `:85 DHom`, `:76 rawDStr_generated`, `:103 dhom_unique_pointwise` | ∅-axiom PURE ✓ (scanned) |
| **★ Ω = the distinguishing-target `Bool`; subobject = decidable predicate** | `Lens/Foundations/FlatOntology.lean:43 Object1 (= χ)`, `:46 Object1_self`, `:60 Type213 := (Fin n → Raw) → Bool`, `:53 Object` | ∅-axiom PURE ✓ (scanned) |
| **★ χ faithful (power-object embedding A → Ω^A); residue = Ω^A diagonal** | `Lens/Foundations/FlatOntologyClosure.lean:47 object1_injective`, `:61 object1_not_surjective`, `:69 self_covering_closure` | ∅-axiom PURE ✓ (scanned) |
| power-object right-inverse / definable round-trip (Ω^A ⇄ A) | `Lens/Foundations/PredicateSelfEncoding.lean:71 predicateToRaw`, `:91 predicate_self_encoding_closure`, `:98 predicateToRaw_kernel` | ∅-axiom PURE ✓ |
| **★★ internal logic intuitionistic — `Bool`/`decide` PURE vs classical `Prop` connectives DIRTY (propext)** | PURE: `Object1` (`decide`), `Type213`, `OnLens.universalMorphismLevelTwo`. DIRTY [propext]: `SemanticAtom.lean:277 propAsDistinguishingAnd`, `:285 canonicalAndMap`, `:299 …Or`, `canonicalIffMap`, `canonicalTruthMap`, `exists_non_lens_expressible` | scan: **43 pure / 23 dirty (all propext)** ✓ |
| Lawvere–Tierney topology `j : Ω → Ω` = the closure operator `clo` | `Lib/Math/Order/GaloisConnection.lean:104 clo`, `:107 clo_extensive`, `:126 clo_idempotent`; adjoint pair `:41 gc_unit`, `:49 gc_counit`, `:79 gc_fgf`, `:91 gc_gfg` | ∅-axiom PURE ✓ (scanned) |
| geometric morphism / point = adjoint reading-pair / unique arrow | `Lib/Math/Order/GaloisConnection.lean gc (F⊣G)`; `Lens/Foundations/SemanticAtom.lean:108 universalMorphism` (a point); `UniversalDistinguishing.lean:85 DHom` (a functor of worlds) | ∅-axiom PURE ✓ |
| `H⁰`/`H^{>0}` poles = q=±1 (internal-logic split = converge/escape) | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`, `:86 multiplier_unimodular`, `:133 escape_residue_outside`, `:160 converge_residue_fixed`, `:228 residue_tag_two_poles` | ∅-axiom PURE ✓ (scanned) |
| cross-frame | `category_theory.md` (variable-set category, initiality), `sheaf_theory.md` (topos = sheaves; gluing = q=+1 initiality; presheaf object absent), `model_theory.md` (internal logic = satisfaction-reading; completeness = view=fold), `yoneda.md` (Ω represents the subobject functor; object = bundle of readings), `galois.md`/`adjunction.md` (clo = Lawvere–Tierney; adjoint = geometric morphism), `measure.md` (the no-Choice structural-account template) | prior, ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):**
`UniversalDistinguishing` (`rawDStr`, `rawDStr_generated`, `dhom_unique_pointwise`, `no_DStr_on_subsingleton`)
— **all PURE**; `SemanticAtom` — **43 pure / 23 dirty** (`universalMorphism`/`_unique`/`raw_initial` PURE;
the **`Prop`-connective** maps `propAsDistinguishing{And,Or,Iff}`/`canonical{And,Or,Iff,Truth}Map`/
`exists_non_lens_expressible` **DIRTY `[propext]`** — the classical-logic cost); `GaloisConnection`
(`clo_extensive`/`clo_idempotent`/`gc_unit`/`gc_counit`/`gc_fgf`/`gc_gfg`) — **all PURE**; `ResidueTag`
(`multiplier_unimodular`/`escape_residue_outside`/`converge_residue_fixed`/`residue_tag_two_poles`) —
**all PURE**. `FlatOntology`/`FlatOntologyClosure` `Bool`-side (`Object1`/`object1_injective`/
`object1_not_surjective`/`self_covering_closure`) — PURE.

## Conceptual-only / absent legs (honest)

- **A NAMED topos / subobject-classifier Ω / power-object / Mitchell–Bénabou language / geometric-morphism /
  Lawvere–Tierney OBJECT — ABSENT, located.** Grep over `lean/E213` for `topos`/`Topos`/`classifier`/
  `Subobject`/`subobject`/`powerObject`/`PowerObject`/`geometricMorphism`/`LawvereTierney`/`Heyting`/
  `TruthValue` returns **zero categorical Lean declarations** (the `Omega` hits are physics — `ZOmega`,
  `OmegaH2Trace` — and the `ω` ordinal; "classifier" only in `DStr`-schema prose). There is no `Topos`
  bundling finite-limits + Ω + power-objects; no `Ω : Type`/`SubobjectClassifier` typed on `Bool` with the
  pullback-of-`true` universal property; no `InternalLanguage`/`MitchellBenabou` translation; no
  `GeometricMorphism`/`LawvereTierneyTopology` on `Bool`. **This is the precise missing leg** — the
  bundled topos and its named Ω + internal language. The *truth-value target* (`Bool`), the *characteristic
  reading* (`Object1`), the *power-object round-trip* (`predicateToRaw`), the *closure modality* (`clo`),
  the *adjoint geometric reading* (`gc`), and the *intuitionistic/classical axiom split* (the propext
  scan) are each built and PURE; the categorical bundle that would name them "a topos" is the open target.
- **The internal logic AS a Heyting-algebra object — ABSENT; the *content* is the PURE/DIRTY axiom split.**
  No `HeytingAlgebra`/`InternalLogic` structure on `Bool` is built. The claim "the internal logic is
  intuitionistic" is grounded *not* by such an object but by the scan fact that the `Bool`/`decide`
  connectives are PURE while the classical `Prop` connectives cost `propext` — i.e. the discipline's own
  ∅-axiom boundary *is* the Heyting/Boolean boundary. The packaged Heyting-algebra-on-Ω theorem is the
  open weld.
- **"213 is constructive BECAUSE it lives in a topos" — a structural reading, certified leg-by-leg.** Lean
  certifies each leg separately (Ω = `Bool`/`Object1` PURE; classical connectives DIRTY-propext; `clo`
  PURE; `raw_initial`/`dhom_unique_pointwise` PURE). The single theorem welding a named `Topos` object to
  "its internal logic is intuitionistic, hence the ∅-axiom no-Classical discipline" is conceptual framing
  on verified PURE/DIRTY facts — the strongest *foundational* prediction in the notebook, and its named
  object is the open leg, the categorical twin of `sheaf_theory.md`'s missing presheaf.

> Axiom-purity note: every theorem cited was scanned with `tools/scan_axioms.py` this session (run from
> repo root with the `E213.` module prefix); the PURE/DIRTY split in `SemanticAtom` (43 pure / 23 dirty,
> all dirties `[propext]`) is the load-bearing evidence for the intuitionistic-internal-logic revelation
> and rests on the fresh scan, not docstrings.
