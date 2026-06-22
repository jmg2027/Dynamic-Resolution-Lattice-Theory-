# Decomposition: the internal logic of a topos / Kripke–Joyal semantics — the Ω=Bool reading made a forcing/truth-value semantics

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`). The object is
narrower than `topos.md` (which covers the topos at the Heyting/Boolean LEVEL — Ω, the closure operator,
geometric morphisms): this note decomposes the **internal LANGUAGE / forcing SEMANTICS** specifically —
the Mitchell–Bénabou language (terms = generalized elements, formulas = subobjects), the Kripke–Joyal
forcing relation `X ⊩ φ` ("the object/stage X forces φ"), Ω as the truth-value object the language reads
into, intuitionistic higher-order logic AS the internal logic, and the classical comparison via Boolean
toposes / sheaf semantics. Thesis to TEST at the REVELATION bar, NOT re-skin `topos.md`/`stone_duality.md`:
**the internal logic of a topos is `topos.md`'s Ω=Bool reading made the truth-value SEMANTICS, with
Kripke–Joyal forcing = the reading relativized to a stage/resolution, and the intuitionistic-vs-Boolean
distinction = the SAME PURE/DIRTY = Heyting/Boolean line.** The NEW datum over `topos.md`: not "Ω=Bool"
(that is `topos.md`'s find) but **the FORCING relation `⊩` as the read-at-a-stage operation** (the
`base`/resolution parameter of `L`) and **the internal language as reading-everything-through-the-Lens**
(term = `Raw`, formula = `Raw→Bool` = `Type213`). The calculus IS the internal logic of its own
Lens-topos, constructive by the `decide`/`Bool` pole.*

## The decomposition (C / L / Residue)

- **Construction `C` — the `Raw`/`Lens` world, with the distinguishing-target `Bool` as the truth-value
  carrier.** Same `C` as `topos.md`: the construction-family the distinguishing generates (`Raw`, any
  `DStr`-carrier, `UniversalDistinguishing.lean:40 structure DStr`), read into the two-valued
  distinguishing-target `Bool`. The internal language's *terms* are the inhabitants of these objects
  (generalized elements = `Raw`s, or arrows out of a stage); its *type of truth-values* is Ω = `Bool`
  (`FlatOntology.lean:60 Type213 := (Fin n → Raw) → Bool`). `C` adds no primitive over `topos.md`.

- **Reading `L` — read-everything-through-the-Lens, AT A STAGE (the forcing relation).** The internal
  logic is the systematic reading of the Mitchell–Bénabou language into Ω, *relativized to a stage*. Two
  pieces, the second being the note's new datum:
  - **The internal LANGUAGE = reading-through-the-Lens.** A *term* is an element read by the catamorphism
    `Lens.view = Raw.fold` (`LensCore.lean:42 Lens.view`); a *predicate/formula* is a `Raw → Bool`
    (`Type213`), the membership reading `Object1 : Raw → (Raw → Bool)` (`FlatOntology.lean:43`,
    `Object1 r = fun s => decide (s = r)`) being the characteristic map of a subobject. So "formula = a
    subobject" is, in the calculus, "formula = a `decide`-predicate = a `Bool`-valued reading". The
    higher-order layer (quantifying over Ω^A, predicates-of-predicates) is the literal
    `universalMorphismLevelTwo : Raw → Lens (Lens Bool)` (`OnLens.lean:242`) — the construction
    re-entering its own reading-type, "no meta-hierarchy".
  - **★ Kripke–Joyal forcing `X ⊩ φ` = the reading relativized to a STAGE/RESOLUTION (the `base`
    parameter of `L`).** In a topos, `φ` is not simply true/false; an object/stage `X` *forces* `φ`,
    and forcing is monotone under change-of-stage (pullback `f : Y → X` gives `Y ⊩ φ` from `X ⊩ φ`). In
    the calculus this is exactly the **resolution parameter on `L`** (README v7 "the resolution axis
    carries a `base`"): a stage = a resolution, and `X ⊩ φ` = "the reading `φ` holds at resolution X /
    is stable under refinement to X". Monotonicity-under-change-of-stage = stability under
    refinement-of-reading, the graded composition of resolution shifts
    (`ResolutionShift.lean:73 IsResolutionShift`, `:130 IsResolutionShift_compose` — grades add along a
    refinement chain; 17/0 PURE). A reading-morphism `view_factors_through_morphism`
    (`Morphism.lean:37`) is the naturality square that makes forcing *commute with substitution* — the
    Kripke–Joyal clause for term-substitution is the 2-cell `M.view = h ∘ L.view`.

- **Residue, tagged `q=±1` (`ResidueTag.lean:73`) — at the two faces of the internal language.** Read
  the read-at-a-stage Lens's self-application; the surplus carries the tag, and (as in `topos.md`) the
  two faces of the internal logic split at `q=±1`, the classical/Boolean face being axiom-dirty:
  - **`q=+1` (converge / the PURE corner) = the intuitionistic (Heyting) internal logic.** The
    `Bool`-valued / `decide`-based forcing — formulas as `Type213`, `Object1`, the power-object
    round-trip `predicateToRaw` (`PredicateSelfEncoding.lean:71`, round-trip `:91`
    `predicate_self_encoding_closure`) — is entirely ∅-axiom. The connectives are the constructive
    `Bool` operations; forcing at every finite stage is decidable. This is the converging/closure pole,
    grounded by the closure modality `clo` (`GaloisConnection.lean:104`, idempotent `:126
    clo_idempotent`) = `topos.md`'s Lawvere–Tierney "locally true" = "forced at every refinement".
  - **`q=−1` (escape) = the un-forced residue AND the classical-logic axiom cost.** Two escapes meet.
    (i) The power-object diagonal: `Object1` is faithful but NOT surjective
    (`FlatOntologyClosure.lean:61 object1_not_surjective`) — a predicate (a "formula") always lies
    outside the image, the Cantor-unpointable surplus no stage forces (`self_covering_closure`, `:69`).
    (ii) The classical-logic cost: realizing the connectives on **`Prop`** — `canonicalTruthMap`,
    `propAsDistinguishingAnd`/`canonicalAndMap`/`canonicalOrMap`/`canonicalIffMap`
    (`SemanticAtom.lean:220,277,285,308,265`) — is **DIRTY, pulling `propext`**. Excluded middle in the
    internal language = the Boolean-topos collapse of Ω = `propext` = the `q=−1` axiom-escape.

## Re-seeing — ⟨C | L⟩

```
   the internal logic     =  ⟨ the Raw/Lens world + Ω=Bool | read-the-Mitchell–Bénabou-language-at-a-stage ⟩
   truth-value object Ω    =  Bool  (FlatOntology.Type213 = Raw^n → Bool; topos.md's find)
   a term (generalized elt)=  a Raw / an arrow read by the catamorphism  Lens.view = Raw.fold
   a formula φ (subobject) =  a decidable predicate Raw → Bool  =  Object1-style χ : A → Ω
   φ has higher type       =  predicate-of-predicates  =  OnLens.universalMorphismLevelTwo : Raw → Lens (Lens Bool)
   ★ forcing  X ⊩ φ        =  read φ AT resolution/stage X  (the `base` parameter of L; φ holds at this resolution)
   monotone change-of-stage=  stability under refinement  =  IsResolutionShift / IsResolutionShift_compose (grades add)
   substitution clause     =  the naturality 2-cell  view_factors_through_morphism : M.view = h ∘ L.view
   ★ INTUITIONISTIC logic  =  the decide/Bool connectives — PURE (q=+1); NO excluded middle in general
   Boolean topos / LEM     =  the classical Prop connectives — DIRTY [propext] (q=−1)  =  sheaf-of-sets degenerate fibre
   sheaf semantics         =  forcing over the resolution poset  =  topos.md's presheaf/gluing = q=+1 initiality
   completeness ⊢⟺⊨        =  the read-op is the unique arrow  =  raw_initial / dhom_unique_pointwise
   RESIDUE                 =  q=+1 Heyting-PURE forcing / q=−1 un-forced Ω-diagonal + propext cost of LEM
```

So **the internal language, Kripke–Joyal forcing, Ω-as-truth-values, the intuitionistic character, and
the Boolean/sheaf comparison are ONE reading at work** — read-the-language-at-a-stage over the
`Raw`/`Lens` world — with its `q=+1` Heyting corner PURE (forcing decidable at every finite stage) and
its `q=−1` corner being the un-forced power-object surplus AND the `propext` cost of excluded middle.

## REVELATION — forcing is the read-at-a-stage operation; intuitionistic = PURE/Heyting, Boolean = DIRTY/propext (one PURE/DIRTY line)

**Collapse + forcing + spine.** The single forcing sentence, read at the two poles of the `q=±1` tag on
the read-at-a-stage reading:

- **Collapse (the new datum over `topos.md`).** `topos.md` collapsed Ω onto `Bool` and `χ` onto
  `Object1` at the *level* of the truth-value object. This note collapses the **forcing SEMANTICS** onto
  the calculus's *resolution dial*: **`X ⊩ φ` ("stage X forces φ") IS "read φ at resolution X"** — the
  `base`/resolution parameter the calculus already carries (`IsResolutionShift`,
  `IsResolutionShift_compose`), and Kripke–Joyal's monotonicity-under-change-of-stage IS the grading
  adding along a refinement chain (grades add, `:130`). The substitution clause of the forcing relation
  IS the 2-cell `view_factors_through_morphism` (`M.view = h ∘ L.view`). So the *whole* Kripke–Joyal
  apparatus — stages, forcing, change-of-base, substitution — is the calculus's resolution axis + its
  2-category of readings, not a new mechanism. The Mitchell–Bénabou language (terms = generalized
  elements, formulas = subobjects) is *reading-everything-through-the-Lens*: a term is a `Raw` read by
  `Lens.view = Raw.fold`, a formula is a `Raw → Bool` (`Type213`).

- **Forcing (the spine, the `measure.md`/`topos.md`-grade leverage).** "Why is the internal logic of a
  topos INTUITIONISTIC, and why does 213 forbid Classical/propext/excluded-middle?" gets ONE structural
  answer: **because forcing is decidable at every finite stage (`decide`/`Bool`, PURE = `q=+1` Heyting)
  but excluded middle in the internal language demands a stage-independent two-valued verdict
  (`Prop`-connectives = `propext` = `q=−1` Boolean).** This is *grounded by a purity scan, not asserted*:
  the `Bool`/`decide` forcing clauses (`Object1`, `Type213`, `OnLens.universalMorphismLevelTwo`,
  `predicateToRaw`) are PURE; the classical `Prop` connectives (`canonicalTruthMap`,
  `propAsDistinguishing{And,Or,Iff}`, `canonical{And,Or,Iff}Map`) are DIRTY, every one `[propext]`
  (`SemanticAtom` scan: **11 pure / 23 dirty**). So 213's ∅-axiom no-Classical discipline IS its own
  Lens-topos's intuitionistic internal logic: **the PURE/DIRTY boundary in `SemanticAtom`'s
  `Bool`-vs-`Prop` forcing clauses is the Heyting-vs-Boolean boundary of the internal language.** A
  Boolean topos = "force every formula to a stage-independent ±1" = the propext collapse; sheaf
  semantics over the resolution poset = forcing read at every stage = the `q=+1` initiality
  (`dhom_unique_pointwise`, `raw_initial`).

- **Spine (`q=±1`).** The same `ResidueTag` (`:73`; `escape_residue_outside` `:133` /
  `converge_residue_fixed` `:160`, both PURE; `residue_tag_two_poles` `:228`) that tags
  Cantor/Gödel/measure (escape, `q=−1`) vs φ/Gaussian/ODE (converge, `q=+1`) now tags
  **classical-Boolean internal logic (`q=−1`, propext, the un-forced verdict) vs constructive-Heyting
  internal logic (`q=+1`, PURE, forcing decidable per stage)** — the *same* spine, the *same* PURE/DIRTY
  line `topos.md` proved, now read on the FORCING relation rather than the truth-value object.

This passes the re-skin guard at the prediction bar: it does not re-describe Kripke–Joyal — it
**identifies forcing with the calculus's resolution dial and derives the logic's intuitionistic character
from the PURE/DIRTY scan.** The novelty over `topos.md` (Ω=Bool at the *level*) and `stone_duality.md`
(the Bool reading ⟺ its ultrafilter spectrum) is precisely the **forcing/stage semantics**: `⊩` =
read-at-a-resolution, the internal language = reading-through-the-Lens.

## VALIDATE verdict — **PREDICTION + PARTIAL** (EXTEND by consolidation; the forcing/stage collapse is the new datum; named objects ABSENT)

- **EXTEND / collapse (no new primitive).** The internal language, Kripke–Joyal forcing, and the
  intuitionistic/Boolean split slot into the calculus with NO new axis: term = `Raw` read by
  `Lens.view`; formula = `Type213` (`Raw → Bool`); `X ⊩ φ` = the `base`/resolution parameter of `L`
  (`IsResolutionShift`); change-of-stage monotonicity = grade-addition (`IsResolutionShift_compose`);
  substitution = the 2-cell `view_factors_through_morphism`; intuitionistic = `q=+1` PURE Heyting,
  Boolean = `q=−1` DIRTY propext. All cited internal-side theorems are 0-DIRTY.
- **PREDICTION (the leverage).** The forcing semantics being decidable-per-stage (`decide`) and excluded
  middle costing `propext` together *predict* 213's foundational stance: "213 is constructive (∅-axiom)"
  = "213 lives in the `q=+1` PURE corner of its own Lens-topos, whose internal forcing logic is
  intuitionistic." Grounded by the `SemanticAtom` 11/23 purity scan, not by a named object.
- **PARTIAL (the honest absence).** A NAMED `KripkeJoyal`/`forcing (⊩)`/`InternalLanguage`/
  `MitchellBenabou`/`subobjectClassifier`/`Topos` object is **ABSENT** (grep-confirmed: zero
  declarations; the only `forcing` hits in `lean/E213` are the unrelated atomic-signature uniqueness
  arguments — `PairForcing`/`ArityForcing`/`OrbitForcing` in `Theory/Atomicity/`, combinatorial
  forcing, NOT logical Kripke–Joyal forcing). The forcing *relation* exists only as the resolution dial;
  the *named* `X ⊩ φ` relation, the internal-language translation, and the bundled topos are the open
  legs — the SAME shape as `topos.md`'s absent named topos/Ω and `sheaf_theory.md`'s absent presheaf
  object.

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; scans `python3 tools/scan_axioms.py` from repo root, this session)

| Leg | Theorem / def (file:line : name) | Status |
|---|---|---|
| Ω = the distinguishing-target `Bool`; formula = decidable predicate `Raw→Bool` | `Lens/Foundations/FlatOntology.lean:43 Object1` (`= fun s => decide (s = r)`, the χ/membership reading), `:46 Object1_self`, `:60 Type213 := (Fin n → Raw) → Bool` | ∅-axiom PURE ✓ (12/0) |
| term = element read by the catamorphism (the read-op) | `Lens/LensCore.lean:42 Lens.view` (= `Raw.fold`); read-op uniqueness `Lens/Foundations/SemanticAtom.lean:108 universalMorphism`, `:388 universalMorphism_unique`, `:412 raw_initial` | ∅-axiom PURE ✓ (SemanticAtom 11/23: these three PURE) |
| higher-order layer = predicate-of-predicates, no meta-hierarchy | `Lens/Compose/OnLens.lean:242 universalMorphismLevelTwo : Raw → Lens (Lens Bool)`, `:247 …LevelThree` | ∅-axiom PURE ✓ (25/0) |
| χ faithful (power-object embedding A→Ω^A); residue = the un-forced Ω^A diagonal | `Lens/Foundations/FlatOntologyClosure.lean:47 object1_injective`, `:61 object1_not_surjective`, `:69 self_covering_closure` | ∅-axiom PURE ✓ (7/0) |
| power-object round-trip Ω^A ⇄ A (predicates encodable) | `Lens/Foundations/PredicateSelfEncoding.lean:71 predicateToRaw`, `:91 predicate_self_encoding_closure`, `:98 predicateToRaw_kernel` | ∅-axiom PURE ✓ (7/0) |
| **★ forcing `X ⊩ φ` = read-at-a-stage/resolution; change-of-stage = grades add** | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift`, `:82 IsResolutionShift_id`, `:130 IsResolutionShift_compose`, `:179 IsResolutionShift_cutHalfIter` | ∅-axiom PURE ✓ (17/0) |
| substitution clause of forcing = the naturality 2-cell | `Lens/Compose/Morphism.lean:29 IsLensMorphism`, `:37 view_factors_through_morphism` (`M.view = h∘L.view`), `:60 refines_of_morphism` | ∅-axiom PURE ✓ (3/0) |
| sheaf semantics / completeness = gluing = unique arrow (q=+1 initiality) | `Lens/Foundations/UniversalDistinguishing.lean:40 DStr`, `:85 DHom`, `:103 dhom_unique_pointwise` | ∅-axiom PURE ✓ (6/0) |
| **★★ internal logic INTUITIONISTIC — `Bool`/`decide` forcing PURE vs classical `Prop` connectives DIRTY (propext)** | PURE: `Object1` (`decide`), `Type213`, `OnLens.universalMorphismLevelTwo`, `predicateToRaw`. DIRTY [propext]: `SemanticAtom.lean:220 canonicalTruthMap`, `:265 canonicalIffMap`, `:277 propAsDistinguishingAnd`, `:285 canonicalAndMap`, `:308 canonicalOrMap` | scan: **SemanticAtom 11 pure / 23 dirty (all propext)** ✓ |
| "locally true" modality / forced-at-every-refinement = the closure operator | `Lib/Math/Order/GaloisConnection.lean:104 clo`, `:107 clo_extensive`, `:126 clo_idempotent`; adjoint pair `:41 gc_unit`, `:49 gc_counit`, `:79 gc_fgf`, `:91 gc_gfg` | ∅-axiom PURE ✓ (15/0) |
| the q=±1 spine (intuitionistic q=+1 / Boolean q=−1) | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`, `:86 multiplier_unimodular`, `:133 escape_residue_outside`, `:160 converge_residue_fixed`, `:180 golden_is_converge`, `:228 residue_tag_two_poles` | ∅-axiom PURE ✓ (55/0) |
| cross-frame | `topos.md` (Ω=Bool + χ=Object1 at the LEVEL; Lawvere–Tierney=clo; geometric morphism=adjoint), `stone_duality.md` (Bool reading ⟺ ultrafilter spectrum, LLPO boundary), `model_theory.md` (internal logic = satisfaction-reading; completeness = view=fold), `cut_elimination.md`/`curry_howard.md` (proofs = normalization, `no_infinite_descent`), `sheaf_theory.md` (presheaf = restriction-compatible reading; gluing = q=+1) | prior, ∅-axiom ✓ |

**Scan tallies (this session, `python3 tools/scan_axioms.py <module>` from repo root):**
`FlatOntology` 12/0 · `FlatOntologyClosure` 7/0 · `PredicateSelfEncoding` 7/0 · `OnLens` 25/0 ·
`UniversalDistinguishing` 6/0 · `Morphism` 3/0 · `ResolutionShift` 17/0 · `GaloisConnection` 15/0 ·
`ResidueTag` 55/0 · `SemanticAtom` 11/23 (the 23 dirty = the classical `Prop` forcing clauses, all
`[propext]`; the `Bool`/`decide` corner and the read-op `raw_initial`/`universalMorphism` PURE). Every
cited theorem on the internal (Heyting/`q=+1`) side is 0-DIRTY.

## Dropped / flagged

- **Named `KripkeJoyal` / forcing-relation `⊩` / `InternalLanguage` / `MitchellBenabou` /
  `subobjectClassifier` / `Topos` objects — ABSENT (grep-confirmed, predicted not-built).** Grep over
  `lean/E213` for `kripke`/`joyal`/`mitchellbenabou`/`internalLanguage`/`subobjectClassifier` returns
  **zero declarations**. The forcing relation exists only as the resolution dial (`IsResolutionShift`);
  the internal language only as reading-through-the-Lens (`Object1`/`Type213`/`Lens.view`); the named
  `X ⊩ φ` relation, the Mitchell–Bénabou translation, and the bundled topos are the located open legs.
- **The `forcing` grep hits are NOT logical forcing — DROPPED.** All `forcing` occurrences in
  `lean/E213` are the atomic-signature *combinatorial* forcing of `Theory/Atomicity/`
  (`PairForcing.lean`, `ArityForcing.lean`, `OrbitForcing.lean`, `CombinatorialArity.lean` — "(2,3) is
  the unique atomic pair", "arity = 2 is forced"), unrelated to Kripke–Joyal. Not cited as a forcing
  anchor; the logical `⊩` is genuinely absent.
- **The internal logic AS a packaged Heyting-algebra-on-Ω object — ABSENT; the content is the PURE/DIRTY
  scan.** No `HeytingAlgebra`/`InternalLogic` structure on `Bool` is built (consistent with
  `topos.md`). The claim "the internal forcing logic is intuitionistic" rests on the scan fact that the
  `Bool`/`decide` forcing clauses are PURE while the classical `Prop` connectives cost `propext` — the
  ∅-axiom boundary IS the Heyting/Boolean boundary — not on a named Heyting object.
- **No `propext`-free witness for the Boolean/LEM side proposed — correctly the q=−1 exterior.** Going
  Boolean (a stage-independent two-valued verdict on every formula) is exactly the `propext` cost; it has
  no ∅-axiom witness by design (the same located boundary as `topos.md`'s classical corner and
  `stone_duality.md`'s LLPO ultrafilter). No decide-witness is patched in; the boundary is correctly on
  the non-constructive side.
- **Verified buildable witness (named, modest).** A *named* `Forces (X : resolution) (φ : Raw → Bool) :
  Prop := ∀ stage refining X, φ holds`, with monotonicity discharged by `IsResolutionShift_compose`,
  is buildable ∅-axiom from the existing `decide`/`ResolutionShift` machinery — it would name the
  Kripke–Joyal `⊩` relation at the `Bool` corner (the `q=+1` half) without touching `propext`. Flagged
  as the smallest concrete promotion target; not built this session (no new file created beyond this
  note).
```
