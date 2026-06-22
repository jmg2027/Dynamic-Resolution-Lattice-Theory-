# Decomposition: a CATEGORY — the calculus's OWN meta-structure (the founding question, answered)

*META-decomposition, per `../README.md` (model v6) and `adjunction.md`. This is the highest-stakes
entry: it decomposes **category theory itself** into `⟨C | L⟩`, which DIRECTLY answers the
originator's founding question — "is the goal to make the axiom into category theory / HoTT?"
(`HANDOFF.md`, "DIRECTION RECALIBRATION" + the CT/HoTT inference, verdict (c) "same content, different
primitive"). `adjunction.md` already found the calculus IS a category of readings; this entry makes
the verdict literal and states precisely what the distinguishing ADDS that bare CT leaves free.*

The previous META-entries decomposed pieces of the calculus's relating-structure (Galois = one
adjoint arrow; adjunction = the closure monad). This entry decomposes the **whole apparatus** — a
category, with objects, morphisms, composition, identity, functors, natural transformations — and
finds it is not a foundation 213 is built *on*, nor a target 213 is *aimed at*, but the shape the
readings-of-a-distinguishing *necessarily form*.

## The decomposition (a category → ⟨C | L⟩)

- **Construction `C`** — a **construction-family**: the constructions a distinguishing-history
  generates (the `Raw`s, or any `DStr`-carrier — `Lens/Foundations/UniversalDistinguishing.lean`
  `DStr`). The objects of "a category" are these constructions; there is no separate "object" entity.

- **Reading `L`** — the **structure-preserving readings** between constructions, *together with how
  they relate*. This is the load-bearing identification, table form:

  ```
     a category            =  ⟨ a construction-family  |  its structure-preserving readings ⟩

     objects               =  constructions                         (Raw / a DStr-carrier)
     morphisms             =  readings (Lens-arrows)                 (Lens.refines / DHom)
     composition           =  series-composition of readings        (refines_trans / DHom ∘)
     identity              =  the trivial reading                    (refines_refl)
     functor               =  a reading OF the reading-structure     (universalMorphism : the
                                                                       unique structure-map)
     natural transformation=  a reading BETWEEN two functors         (pointwise reading-comparison,
                                                                       dhom_unique_pointwise's shape)
  ```

- **Residue** — what the reading-structure forces but cannot capture is the **self-cover gap**: the
  category of readings-of-`C` never encloses `C` from inside any one reading
  (`FlatOntologyClosure.object1_not_surjective` — the self-cover is faithful but never total). The
  residue is the calculus's `q=±1`-tagged surplus (`adjunction.md`): the **closure/converging** corner
  (`q=+1`, `clo_idempotent`) is the categorical apparatus that *settles* (limits, monads, the
  fundamental-theorem bijection); the **escaping** corner (`q=−1`, the diagonal) is the colimit/free
  side the category leaves open-ended.

## Re-seeing — the categorical apparatus, term by term, as proven readings-structure

Every piece of "a category" is already a proven object in this repo, reached from the distinguishing:

- **Morphisms compose / identity exists** — readings form a (thin) **category**: `Lens.refines`
  (`Lens/LensCore.lean`) with `Lens.refines_refl` (identity) and `Lens.refines_trans` (composition),
  and a **groupoid core** `LensIso` with `lensIso_refl/symm/trans` (`Lens/Unified.lean`). The category
  *and* groupoid laws are bare list/kernel identities — no axiom, no `funext`.

- **Initial object + the read-operation are ONE** — `raw_initial` (`Lens/Foundations/SemanticAtom.lean`)
  proves `Raw` is the **initial object**: for every `HasDistinguishing α` there is a *unique* arrow
  `universalMorphism α : Raw → α` (`universalMorphism_unique`), and that unique arrow **is the
  catamorphism** `Raw.fold` (`Theory/Raw/Fold.lean`, `= Lens.view`). So "read a construction through a
  reading" = "the unique morphism out of the initial object." The categorical primitive *is* the
  calculus's read-primitive — they were never two things (this is the deepest collapse: the founding
  question's resolution in one theorem).

- **Functor = a reading of the reading-structure** — `universalMorphism (Lens Bool) : Raw → Lens Bool`
  (`Lens/Compose/OnLens.lean`) is the construction re-entering its *own reading type*: no
  meta-hierarchy, `Lens` is just another `DStr`-instance, so a functor (a structure-map between
  reading-categories) is the same `universalMorphism` schema one level up. The schema-level statement
  is `DStr` + `DHom` (`UniversalDistinguishing.lean`): a `DHom` is a structure-preserving map of
  distinguishing-carriers — a functor between two construction-families.

- **Natural transformation = a reading between functors** — `dhom_unique_pointwise`
  (`UniversalDistinguishing.lean`): any two `DHom`s out of the free/generated `rawDStr` are *pointwise
  equal*. A natural transformation is the pointwise comparison of two such structure-maps; here the
  comparison is forced (initiality makes the only natural transformation the identity), which is
  *exactly* why `Raw` is initial.

- **Adjunction / monad** — `adjunction.md` (grounded): `gc` (`Order/GaloisConnection.lean`) is an
  adjoint pair `F ⊣ G` (`gc_unit` = η, `gc_counit` = ε, `gc_fgf`/`gc_gfg` = triangle identities), and
  `clo = G∘F` with `clo_extensive` (η) + `clo_idempotent` (μ: `T²=T`) **is the idempotent monad** the
  adjunction generates — *proved before being named*. The Yoneda-flavoured representability slogan
  ("universal property lives on the closure-algebras", `closed_iff_image`) is the one earned
  prediction.

So the entire list (objects, morphisms, ∘, id, functor, nat-trans, initial object, adjunction, monad)
is present, ∅-axiom, and reached from the single act of distinguishing — not imported.

## THE REVELATION (the founding question answered)

**"Is 213 category theory / HoTT?" resolves as: the calculus IS category-theory-shaped, but
GENERATED FROM the distinguishing primitive — not built on CT, not aimed at CT.** Verdict (c) of the
HANDOFF inference ("same content, different primitive") is here made *literal*, term by term: the
categorical apparatus is precisely what the readings-of-a-distinguishing necessarily form. `Raw` is
the initial object (`raw_initial`), `Raw.fold`/`universalMorphism` is the catamorphism = the unique
arrow out of it = the read-operation itself, readings are the morphisms (`Lens.refines`,
`refines_refl`/`refines_trans` = a category; `LensIso` = its groupoid), adjoint reading-pairs generate
the idempotent closure monad (`clo`, `clo_idempotent`, `gc_fgf`/`gc_gfg`). Category theory is the
calculus's own meta-structure — so 213 does not *become* CT and is not *reducible* to it; the
categorical shape is the **forced unfolding of the distinguishing**, the same content reached from a
different primitive. (HoTT is **absent and structurally opposed**: `propext`/`Quot.sound`/`funext` are
forbidden, so the calculus's equivalence is the 1-categorical kernel preorder `Lens.refines`, not
univalence — `equivalence.md`'s "honest 1-categorical ceiling.")

**What the distinguishing ADDS that bare CT does not have** — this is the payoff, and the answer to
"different primitive": bare category theory leaves three things as *free choices*; the distinguishing
*forces* all three as ∅-axiom theorems.

1. **The `q=±1` residue bit.** CT has limits and colimits as independent, unforced data. The calculus
   has *one* residue read at two unimodular poles: the **escaping** residue (Cantor diagonal,
   fixed-point-free, `q=−1`, `OneDiagonal.no_surjection_of_fixedpointfree`,
   `FlatOntologyClosure.object1_not_surjective`) and the **converging/closure** residue (φ, `clo`,
   `q=+1`) are the *same* object at the two signs — `CassiniUnimodular.cassini_law_one_at_two_multipliers`
   proves the dichotomy is *one parametric law* `det_step` at `q=+1` vs `q=−1`. CT's
   limit/colimit duality is, here, *derived* from the single multiplier bit, not posited.

2. **Atom-(in)distinguishability.** CT's objects are featureless dots; what makes a hom-set
   *structured* is extra data the theory does not supply. The distinguishing supplies it: `×`-atoms
   (primes) are **distinguishable** — `Meta/Nat/FoldCriterion.two_three_unique` (`2^a = 3^b → a=0 ∧
   b=0`) forces a per-prime axis — while `+`-atoms (units) are **indistinguishable**
   (`UnitList.append_comm`). This is *why* one construction carries a vector readout and another a
   scalar one (`prime_factorization.md`); CT leaves "what the objects are made of" free.

3. **The forced shape `(NS, NT, d) = (3, 2, 5)`.** CT picks its base category, its generating object,
   its dimension — all free. The distinguishing forces a *unique* self-consistent shape:
   `Meta/ThreeDirectionUniqueness.three_direction_uniqueness` bundles (i) 4-clause minimality — every
   clause essential, (ii) universal-Lens factoring — every distinguishability framework factors through
   `Raw` via an injective view (the "sideways" initiality), and (iii) `Atomic n ↔ n = 5` with the
   pair-forcing `(NS, NT) = (3, 2)` ("above"). Bare CT has no analogue of "the base shape is forced";
   the distinguishing does, and it is one ∅-axiom theorem.

Net: **CT = the calculus's meta-structure; the distinguishing = the forced CONTENT that meta-structure
leaves as free choices.** 213 is category-theory-shaped *because* the readings of one self-grounding
act necessarily form a category — and it adds, beyond bare CT, the `q=±1` residue, atom
distinguishability, and the forced `(3,2,5)` skeleton.

## Note for the technique — does decomposing CT close the loop?

**Yes, with a precise and honest seam.** Decomposing category theory into `⟨C | L⟩` is the calculus
turning on *itself* — and it succeeds: the calculus is **self-describing**, its own apparatus
(initial object, catamorphism, adjunction, closure monad, groupoid) is the very vocabulary it produces
for everything else (`adjunction.md`'s "the repo proved the monad before naming it"). This is the
strongest possible pass of the README's revelation-rule (re-skin guard): the decomposition is not a
re-labelling, it is a **fixed point** — feeding the technique its own structure returns that structure,
certified by `raw_initial` + `dhom_unique_pointwise` (initiality makes the self-reading unique).

But the loop closes *only on the `q=+1` (converging/closure) corner*, and saying so is the honesty
the calculus requires. Grounded: the initial object, the catamorphism-as-read, the thin category +
groupoid of readings, the idempotent closure monad. Conceptual-only (open Lean targets, flagged in
`adjunction.md` and the frontier): the **free monad** (no `Lens.bind`/Kleisli in `LensCore.lean`), the
**colimit/`q=−1` growing** side packaged as a category-with-all-(co)limits, and HoTT-level higher
coherence (forbidden by the `funext`-free discipline). So the loop is closed for "the category of
**residues that converge**" — the same `q=+1` asymmetry every prior META-entry hit. The distinguishing
*does* supply a growing endofunctor (`MuNuMirror.succ_not_idempotent`, the README's batch-after-v5
find), so the free corner is not *empty* — only the monad *multiplication* there is un-built. The
self-description is complete on the corner the repo has proven and honestly partial on the corner it
has not; that the seam falls exactly at `q=±1` is itself the confirmation that the calculus's own
meta-structure obeys the calculus.

## Verified Lean anchors (all grep-checked)

Category / groupoid of readings:
- `Lens/LensCore.lean`: `Lens.refines` (def), `Lens.refines_refl` (identity), `Lens.refines_trans`
  (composition) — the thin category; `Lens.view` (= the catamorphism)
- `Lens/Unified.lean`: `LensIso`, `lensIso_refl`/`lensIso_symm`/`lensIso_trans` (groupoid),
  `lensIso_iff_kernel_eq`

Initial object + catamorphism = the read-operation:
- `Lens/Foundations/SemanticAtom.lean`: `raw_initial` (Raw is initial), `universalMorphism` (the unique
  arrow), `universalMorphism_unique`, `universalMorphism_slash` (homomorphism law)
- `Theory/Raw/Fold.lean`: `Raw.fold` (catamorphism), `Raw.fold_slash`
- `Lens/Compose/OnLens.lean`: `universalMorphism (Lens Bool) : Raw → Lens Bool` (functor = reading of
  the reading-type; "no meta-hierarchy")

Functor / natural-transformation schema (DStr / DHom):
- `Lens/Foundations/UniversalDistinguishing.lean`: `DStr` (the distinguishing schema = a category of
  carriers), `rawDStr`, `rawDStr_generated` (Raw = free DStr), `DHom` (structure-preserving map =
  functor), `dhom_unique_pointwise` (the only nat-trans out of the free object — initiality),
  `no_DStr_on_subsingleton` (the negative arm)

Adjunction / closure monad (the `q=+1` corner):
- `Lib/Math/Order/GaloisConnection.lean`: `gc_unit` (η), `gc_counit` (ε), `gc_fgf`/`gc_gfg` (triangle
  identities), `clo` (= G∘F), `clo_extensive`, `clo_idempotent` (μ: T²=T); `mulDiv_gc` (witness)
- `Lib/Math/Order/GaloisConnectionComposition.lean`: `gc_comp`, `closed_iff_image`, `gc_le_closed`

What the distinguishing ADDS (forced beyond bare CT):
- `Lib/Math/Algebra/CassiniUnimodular.lean`: `cassini_law_one_at_two_multipliers` (the `q=±1` residue
  is one law `det_step` at two multipliers — limit/colimit duality forced)
- `Lens/Foundations/FlatOntologyClosure.lean`: `object1_not_surjective` (the self-cover residue,
  faithful-but-never-total); `Lens/Foundations/OneDiagonal.lean`: `no_surjection_of_fixedpointfree`
  (the `q=−1` escaping pole)
- `Meta/Nat/FoldCriterion.lean`: `two_three_unique` (×-atom distinguishability)
- `Meta/ThreeDirectionUniqueness.lean`: `three_direction_uniqueness` (the forced `(NS,NT,d)=(3,2,5)`
  shape — below/sideways/above, one ∅-axiom theorem)

## Conceptual-only legs (honest — NOT grounded in repo Lean)

- **Free monad / Kleisli on readings** — no `Lens.bind`, no Kleisli composition in `LensCore.lean`
  (confirmed in `adjunction.md`). Only the *idempotent closure* monad is grounded. The `q=−1`/free
  monad *multiplication* is an open target; the growing endofunctor itself is real
  (`MuNuMirror.succ_not_idempotent`).
- **Category-with-all-(co)limits** — `Lens/Lattice/` has products/joins (`iProdLens`/`iJoinLens`) by
  file presence, but no packaged completeness theorem; only `raw_initial` (the initial *object*) is
  grounded.
- **Yoneda lemma / representability proper** — only the closure-algebra localization
  (`closed_iff_image`) is grounded; full Yoneda is conceptual.
- **HoTT / univalence / identity-types / HITs** — entirely absent and *structurally forbidden*
  (`funext`/`propext`/`Quot.sound` disallowed). The calculus's equivalence is the 1-categorical kernel
  preorder `Lens.refines` (`equivalence.md`), a deliberate ceiling, not an omission.
