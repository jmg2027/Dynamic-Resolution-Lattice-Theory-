# Decomposition: the Yoneda lemma / representable functors — the calculus describing ITSELF

*META-decomposition, per `../README.md` (model v7.1), `category_theory.md` (213 is
category-theory-shaped, generated from the distinguishing: `Raw` = initial object,
`Lens.view = Raw.fold` = catamorphism, readings = morphisms), `two_cells.md` (readings form a
2-category; nat-trans = `view_factors_through_morphism`), and `equivalence.md` (one Lens-arrow,
`lensIso_iff_kernel_eq`). This is the highest-stakes entry of all: Yoneda is the formal statement
that **an object is its bundle of maps** — which is the calculus's own founding sentence,
`OBJECT = ⟨Construction | Reading⟩`. Decomposing Yoneda is the calculus reading its OWN operating
principle back to itself. The expected outcome is not a new field but a **fixed point**: feed the
technique its self-description, get that self-description certified.*

## The decomposition (Yoneda → ⟨C | L⟩)

- **Construction `C`** — an object `A` of the category, i.e. (per `category_theory.md`) a
  construction the distinguishing generates — a `Raw`, or any `DStr`/`HasDistinguishing` carrier.
  In the calculus's own terms `A` is the *thing being read*, the operand of every reading.

- **Reading `L`** — the **probe-bundle reading**: `A ↦ Hom(−, A)` (covariant: `A ↦ Hom(A, −)`),
  read each construction *by how everything maps into/out of it*. This is the calculus's foundational
  move stated as a reading:

  ```
     Yoneda embedding   A ↦ Hom(−, A)   =   ⟨ A | the reading "what every probe reveals of A" ⟩

     an object A                  =  a construction                       (Raw / a DStr-carrier)
     Hom(−, A)                    =  the bundle of A's readings           (the maps INTO A)
     the embedding is FAITHFUL    =  the reading separates objects        (object1_injective)
     the embedding is FULL        =  every nat-arrow of bundles ← a map   (refines_of_morphism)
     Nat(Hom(A,−), F) ≅ F(A)      =  a reading out of A is pinned by ONE   (dhom_unique_pointwise)
                                       element — initiality of the probe
     the universal element        =  the q=+1 fixed point of the reading  (raw_initial / clo)
     representability of F         =  F IS a reading (a Lens)             — F = Hom(−,A) for some A
  ```

- **Residue** — what the probe-bundle reading forces but cannot capture is the **self-cover gap**:
  the bundle of readings is *faithful* (an object IS recovered from its probes — surjective ONTO its
  readings) but the global self-cover is *never total* — `FlatOntologyClosure.object1_not_surjective`.
  So Yoneda's positive content (object = its maps) and the calculus's residue
  (`object1_not_surjective`) are **the two halves of one theorem**: faithful where it embeds,
  un-total where the self-application diagonalizes out. Yoneda is `object1_not_surjective`'s
  **positive twin** — the where-it-succeeds to the residue's where-it-fails.

## Re-seeing — Yoneda, term by term, as proven readings-structure

Every load-bearing piece of Yoneda is an already-proven ∅-axiom object in this repo, because Yoneda
is not *about* the calculus's apparatus — it **is** the calculus's apparatus stated reflexively.

- **"An object is determined by its maps" = the calculus's founding sentence.** The README's normal
  form is `OBJECT = ⟨C | L⟩` — an object is a construction *read through* its readings; there is no
  object-in-itself behind the readings. This is precisely the Yoneda slogan ("an object is the bundle
  of its maps"). The calculus did not adopt Yoneda; the calculus's first axiom *is* the Yoneda
  principle, and `equivalence.md` already states the consequence: "sameness is never a property of
  constructions, always a reading laid over a pair."

- **Faithfulness = the reading separates objects = `object1_injective`.** The Yoneda embedding being
  *faithful* means: distinct objects have distinct probe-bundles — the reading does not collapse two
  objects. The calculus proves exactly this for its canonical self-cover `Object1 : Raw → (Raw → Bool)`
  (each `Raw` read as its own self-indicator): `object1_injective` (`FlatOntologyClosure.lean:47`,
  PURE) — distinct `Raw`s give distinct indicator predicates. The self-cover is *faithful* — the
  distinguishing succeeds, objects ARE recovered from how they are read. This is Yoneda faithfulness
  in the calculus's own self-cover.

- **Fullness / "same readings ⟹ isomorphic" = `lensIso_iff_kernel_eq`.** Yoneda fullness +
  faithfulness gives the corollary the calculus leans on most: two objects with the *same* bundle of
  readings are isomorphic. `equivalence.md`'s `Unified.lensIso_iff_kernel_eq` (`Unified.lean:64`,
  PURE) is exactly this — `LensIso L M ↔ ∀ x y, L.equiv x y ↔ M.equiv x y`: two readings are
  isomorphic **iff their kernels coincide**, i.e. iff they reveal the same fibres. "Reading
  determines object up to iso" IS the Yoneda corollary, and it is a kernel-coincidence theorem, not a
  separate primitive. A 2-cell of bundles is induced by a map (`refines_of_morphism`,
  `Morphism.lean:60`, PURE: an `IsLensMorphism h L M` *induces* `L.refines M`) — fullness's
  direction, that bundle-arrows come from object-maps.

- **The Yoneda lemma `Nat(Hom(A,−), F) ≅ F(A)` = `dhom_unique_pointwise` (initiality).** The Yoneda
  lemma says: a natural transformation *out of* a representable `Hom(A,−)` is determined by a *single*
  element — its value `F(A)` on the identity `1_A`. In the calculus the representable is the **free /
  initial** object `Raw` (`raw_initial`, `SemanticAtom.lean:412`, PURE: for every
  `HasDistinguishing α` there is a *unique* distinguishing-preserving `Raw → α`), and a natural
  transformation out of it is a `DHom rawDStr N`. `dhom_unique_pointwise`
  (`UniversalDistinguishing.lean:103`, PURE) proves any two such structure-maps **agree pointwise** —
  the arrow out of the representable/free object is *unique*, pinned by its action on the generators
  (the bases + the one combine rule). That "pinned by one datum" IS the Yoneda lemma's content:
  `Nat(out of the representable) ≅ (one element)`. The bijection is the uniqueness theorem read as a
  natural iso. `two_cells.md` already cited this as "the only 2-cell out of `Raw` is the identity" —
  Yoneda is that statement named.

- **A reading out of the representable factors = `view_factors_through_morphism`.** The "Nat(...) is
  one element" bijection's *naturality* is the triangle `M.view r = h(L.view r)`
  (`view_factors_through_morphism`, `Morphism.lean:37`, PURE) — a reading `M` factors through a
  reading `L` via the component `h`. This is the naturality square of the Yoneda iso over the single
  initial object, the same anchor `two_cells.md` identified as the natural-transformation law.

- **Representability = "the functor IS a reading (a Lens)".** A presheaf `F` is *representable* iff
  `F ≅ Hom(−, A)` for some `A` — iff it has a *classifying* object. In the calculus a functor "is a
  reading" iff it is a `Lens` (a `Raw → α`), i.e. iff it arises as `universalMorphism α`
  (`SemanticAtom.lean:108`, PURE) — the unique catamorphism out of the initial object — for some
  carrier `α`. Representability = "the reading has a construction that classifies it" = the functor
  factors through `Raw.fold`/`Lens.view`. The **universal element** (the image of `1_A`, the datum
  the Yoneda lemma extracts) is the reading's `q=+1` fixed point: the value the reading *settles on*,
  delivered by initiality (`raw_initial`) and, in the relating layer, by the idempotent closure `clo`
  (`adjunction.md`/`category_theory.md`, the `q=+1` converging corner).

So the entire Yoneda package (embedding, faithfulness, fullness, the lemma, the universal element,
representability) is present, ∅-axiom, and is the calculus's **own** vocabulary — not an imported
field. The decomposition is the technique applied to its own first sentence.

## THE REVELATION — Yoneda is the calculus's self-description; a FIXED POINT, certified

**Yoneda is not a new field to decompose. It is the calculus's OWN operating principle made
categorical — and decomposing it returns the calculus's own foundations, certified by the four
theorems the calculus is built on.** This is the strongest possible pass of the README's
revelation-rule (the re-skin guard): the decomposition is a **fixed point** — feed the technique its
self-description (`OBJECT = ⟨C | L⟩`, "an object is its readings") and you get back exactly that,
pinned by:

- the **Yoneda embedding** `A ↦ ⟨A | its reading-bundle⟩` = the calculus's founding sentence
  `OBJECT = ⟨C | L⟩`, with **faithfulness = `object1_injective`** (distinct objects, distinct
  bundles — the self-cover succeeds);
- the **Yoneda lemma** `Nat(Hom(A,−),F) ≅ F(A)` = **`dhom_unique_pointwise`** (an arrow out of the
  representable/initial object is pinned by one datum — uniqueness of the catamorphism), with its
  naturality = **`view_factors_through_morphism`**;
- **fullness / "same readings ⟹ iso"** = **`lensIso_iff_kernel_eq`** (object recovered up to iso from
  its kernel of readings) — `equivalence.md`'s collapse is Yoneda's corollary;
- the **residue** = **`object1_not_surjective`**, Yoneda's *negative twin*: the probe-bundle is
  faithful (surjective onto the object's readings — Yoneda) yet the global self-cover is never total
  (the Cantor diagonal — the calculus's `q=−1` residue). **Yoneda and the residue are the two halves
  of one theorem `self_covering_closure`** (`FlatOntologyClosure.lean:69`, PURE: injective ∧
  ¬surjective) — faithful where it embeds, un-pointable where self-application escapes.

So the calculus's deepest self-statement is: **`self_covering_closure` = Yoneda ⊕ its residue in one
∅-axiom line.** `object1_injective` (Yoneda faithfulness, the object IS its readings) and
`object1_not_surjective` (the residue, a reading always lies outside the image) are the two
conjuncts. Yoneda is the calculus describing itself; the residue is where that self-description
provably cannot close — and that is not a defect but the content of `01_residue.md`. **The calculus
is self-describing, and Yoneda is the name of the self-description.** (`category_theory.md`'s closing
note — "the loop closes only on the `q=+1` corner" — is here made precise: Yoneda's *positive* lemma
lives in the `q=+1` settling corner (`dhom_unique_pointwise`, the unique settled arrow); its
*residue* is the `q=−1` escaping corner (`object1_not_surjective`). Yoneda is the seam itself.)

## Note for the technique — what Yoneda ADDS to `category_theory.md`'s self-loop

`category_theory.md` decomposed the *apparatus* (initial object, catamorphism, monad) and found
self-description. This entry decomposes the *one theorem that names why* the apparatus is
self-describing: an object IS its maps. Yoneda is the load-bearing reason the calculus can read
itself — because in a Yoneda-world there is no object-behind-the-readings to be left out. The
calculus's `OBJECT = ⟨C | L⟩` is a *commitment to the Yoneda principle as ontology*: a construction
has no content beyond what its readings reveal (and the residue is exactly the proven surplus that
no single reading reveals, `object1_not_surjective`). The honest seam is the same one every META-entry
hits: the *positive* Yoneda lemma is `q=+1` (the unique settled arrow, `dhom_unique_pointwise`) and is
fully built; the *residue half* (`q=−1`) is built as the negation theorem but the colimit/free corner
that would package "presheaves = the free cocompletion" is not.

## Verified Lean anchors (all grep-checked + axiom-scanned this session)

| Anchor (theorem / def) | File:line | Role in this decomposition | Purity |
|---|---|---|---|
| `object1_injective` | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:47` | **Yoneda FAITHFULNESS** — distinct objects have distinct reading-bundles (the self-cover separates) | PURE (scanned) |
| `object1_not_surjective` | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61` | **the RESIDUE, Yoneda's negative twin** — a reading always lies outside the self-cover's image (Cantor, `q=−1`) | PURE (scanned) |
| `self_covering_closure` | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:69` | ★ **Yoneda ⊕ residue in one line** — injective ∧ ¬surjective: faithful where it embeds, un-total where it escapes | PURE (scanned) |
| `dhom_unique_pointwise` | `lean/E213/Lens/Foundations/UniversalDistinguishing.lean:103` | ★ **the YONEDA LEMMA** — an arrow out of the representable/initial object is pinned by one datum (any two `DHom rawDStr N` agree pointwise) | PURE (scanned) |
| `raw_initial` | `lean/E213/Lens/Foundations/SemanticAtom.lean:412` | the representable object = the **initial/free** object `Raw`; the universal element = the unique arrow's existence | PURE (scanned) |
| `universalMorphism` / `universalMorphism_unique` | `lean/E213/Lens/Foundations/SemanticAtom.lean:108,388` | the unique catamorphism = the read-out of the representable; representability = "F arises as this for some carrier" | PURE (scanned) |
| `view_factors_through_morphism` | `lean/E213/Lens/Compose/Morphism.lean:37` | naturality of the Yoneda iso — `M.view r = h(L.view r)` (the bundle-naturality triangle) | PURE (scanned) |
| `refines_of_morphism` | `lean/E213/Lens/Compose/Morphism.lean:60` | **fullness direction** — a bundle-arrow `IsLensMorphism h L M` induces an object-arrow `L.refines M` | PURE (scanned) |
| `IsLensMorphism` | `lean/E213/Lens/Compose/Morphism.lean:29` | the component map + naturality squares — the data a Yoneda natural transformation carries | PURE (scanned) |
| `lensIso_iff_kernel_eq` | `lean/E213/Lens/Unified.lean:64` | **Yoneda corollary** — "same reading-bundle ⟹ isomorphic": `LensIso ↔` kernel coincidence | PURE (scanned) |
| `LensIso` / `lensIso_refl/symm/trans` | `lean/E213/Lens/Unified.lean:42,46,50,54` | the groupoid of invertible bundle-comparisons (Yoneda iso lives here) | PURE (scanned) |
| `DStr` / `DHom` / `rawDStr_generated` | `lean/E213/Lens/Foundations/UniversalDistinguishing.lean:40,85,76` | functor/presheaf schema (carriers + structure-maps); `Raw` = the free representable | PURE (scanned) |

## Conceptual-only legs (honest — NOT grounded in repo Lean)

- **A NAMED Hom-functor / Yoneda embedding / presheaf object.** The repo has **no** `Hom(−,A)` functor
  object, no `よ`/Yoneda embedding `def`, no `Presheaf`/`PSh(C)` type. (The string "representable" in
  Lean occurs only in *number-theoretic* senses — Frobenius-representable, sum-of-two-squares — never
  as a categorical Hom-functor; `category_theory.md:202–203` already flagged "full Yoneda is
  conceptual".) The **content** is foundational regardless: the Yoneda *principle* is the calculus's
  first axiom (`OBJECT = ⟨C | L⟩`), and its four formal pillars (faithfulness `object1_injective`,
  the lemma `dhom_unique_pointwise`, fullness `lensIso_iff_kernel_eq`, the residue
  `object1_not_surjective`) are all PURE theorems — but the *packaged categorical statement*
  "`Nat(Hom(A,−),F) ≅ FA` as a natural iso of presheaf objects" is not a single theorem. The precise
  missing leg: an explicit **Hom-functor object** and the **presheaf category** `PSh(C)`, which would
  require the free-cocompletion / colimit corner the calculus has only built the `q=+1` half of.
- **The universal element as an extracted natural iso.** `raw_initial` + `dhom_unique_pointwise`
  give the *existence + uniqueness* (the universal element exists and pins the arrow), but the Yoneda
  bijection `Nat(Hom(A,−),F) → F(A), η ↦ η_A(1_A)` is not built as an explicit `Equiv` (and an
  `Equiv` of nat-transformation *types* would press on `funext`, which the discipline forbids — the
  same `q=±1`/HoTT ceiling `equivalence.md` and `category_theory.md` record). Pointwise uniqueness is
  the funext-free shadow that is actually proved.

## Cross-frame

`category_theory.md` (the apparatus is self-describing; Yoneda is the *named reason* — object = its
maps — and lives at the same `q=±1` seam); `equivalence.md` (`lensIso_iff_kernel_eq` = Yoneda's
"same readings ⟹ iso" corollary; the 1-categorical ceiling = why the full Yoneda *Equiv* is
funext-blocked); `two_cells.md` (`view_factors_through_morphism` = the Yoneda iso's naturality;
`dhom_unique_pointwise` = the only arrow out of the representable); `cardinality.md`/`godel.md`
(`object1_not_surjective`'s `q=−1` escape = Yoneda's residue half, the diagonal that the faithful
embedding cannot enclose). **VERDICT: PREDICTION** — Yoneda = the calculus's own operating principle
made categorical, a self-describing fixed point: embedding = `⟨C|L⟩`, lemma = `dhom_unique_pointwise`,
fullness = `lensIso_iff_kernel_eq`, faithfulness = `object1_injective`, residue =
`object1_not_surjective`, with `self_covering_closure` bundling Yoneda ⊕ residue in one ∅-axiom line.
The single precise absence: a *named* Hom-functor / presheaf object (the `q=−1` cocompletion corner).
