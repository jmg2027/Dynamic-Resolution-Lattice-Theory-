# Decomposition: motives / motivic cohomology (Grothendieck's universal cohomology, pure motives, the category of motives as the universal target of every Weil cohomology, realizations Betti/de Rham/ℓ-adic as functors out of motives, the motivic Galois group, the conjectural Tannakian structure)

*A FRESH decomposition per `../README.md` (model v7.1), the most **reflexive** entry in the notebook.
The hypothesis to **test, not re-skin**: a motive IS the calculus's **universal Lens** — the literal
universal factorization `Lens.view = Raw.fold` (`raw_initial` / `dhom_unique_pointwise`) *named in the
cohomology setting*. Grothendieck's slogan — "the universal cohomology theory through which every Weil
cohomology factors uniquely" — is, term for term, the calculus's CORE theorem: `raw_initial` says
`Lens.view = Raw.fold` is the **unique** arrow out of `Raw`, so **every reading factors through the
universal distinguishing**. Motives = that universality, instanced on cohomology. Where
`homological_algebra.md` named the calculus's **residue-taking operation** (`Residue(L,C)` graded by `n`),
this note names the calculus's **universal-factorization** mechanism. They are the two halves of the
README normal form `⟨C|L⟩ ⊕ Residue(L,C)`: motives = the `⟨C|L⟩` factorization (which `C` every reading
passes through), homological algebra = the `Residue` half (what each reading leaves). This is the field
where the calculus recognizes its own engine.*

## The decomposition (C / Reading / Residue)

- **Construction `C` — the category of motives = the universal `C`/`Raw`, the thing every reading is
  read OUT of.** Grothendieck's motive is not "another cohomology" — it is the *target* through which all
  the others factor: you build it once, and each Weil cohomology is then a functor *out* of it. In the
  calculus that role is occupied by exactly one object: **the universal distinguishing `Raw`** (`Theory/Raw`),
  with `Lens.view r = r.fold L.base_a L.base_b L.combine` (`LensCore.lean:42`) the unique read-out, and
  `raw_initial` (`SemanticAtom.lean:412`) the theorem that `Raw` is **initial** — for any reading-target
  `α`, the distinguishing-preserving `Raw → α` *uniquely* exists. So "the category of motives = the
  universal cohomology every other factors through" is the cohomology-clothed reading of "`Raw` = the
  initial object every Lens reads out of". Concretely the cohomological `C` is the **chain/cochain
  complex** of `homological_algebra.md` (`Cochain n k`, the boundary `delta`, `Delta/Core.lean`), carrying
  the README's two read-off axes — a **fold-height** (the cohomological degree / weight) and a
  **direction/orientation bit** (the `q=±1` alternating sign). A motive is "a piece of that complex
  considered universally, before any one cohomology reads it". **No `Motive`, no `WeilCohomology`, no
  abelian/Tannakian-category object enters** (see verdict) — the universal `C` is `Raw` + its complex.

- **Reading `L` — a realization is a Lens on the SAME motive `C`.** This is the precise content. A Weil
  cohomology (Betti, de Rham, ℓ-adic) is a *functor out of motives* — in the calculus, a **reading `L`
  factoring through the universal `C`**. The factorization is not metaphor: `view_factors_through_morphism`
  (`Compose/Morphism.lean:37`, **PURE**) is, term for term, *if `h` is a Lens-morphism then
  `M.view r = h (L.view r)` for all `r`* — a coarser reading `M` is the finer reading `L` followed by a
  forgetful `h`. The realizations Betti/dR/ℓ-adic are different `M`'s factoring through one finer reading
  — i.e. **the SAME `C` read different ways**, which is exactly `homological_algebra.md`'s "homology /
  de Rham / sheaf are three outputs of one machine" promoted to the universal statement. The "comparison
  isomorphisms" between realizations (Betti ≅ de Rham over ℂ) are the kernel-equality of two Lenses:
  `lensIso_iff_kernel_eq` (`Unified.lean:64`, PURE) says two readings are isomorphic iff they induce the
  same kernel on `Raw` — two realizations agree iff they identify the same motivic data. So:
  - **a motive** = an element/piece of the universal `C` (`Raw`/the complex);
  - **a realization** = a reading `L` (a Lens), factoring through `C` by `view_factors_through_morphism`;
  - **Betti / de Rham / ℓ-adic** = three `L`'s on one `C` (the comparison isos = `lensIso_iff_kernel_eq`).

- **Residue — the `q=±1` standard-conjectures gap: that the universal factorization is faithful/full.**
  The motivic story has a built-in conjectural residue: the standard conjectures / the claim that
  numerical and homological equivalence coincide / that motives form an honest **Tannakian** category with
  a well-defined **motivic Galois group**. In the calculus this is exactly the `q=±1` residue of the
  universal Lens read on *itself*. The universal distinguishing is **faithful** (`object1_injective`,
  `FlatOntologyClosure.lean:47`) — the `q=+1` converging pole: distinct motives are genuinely separated,
  the realization records them — **and never total** (`object1_not_surjective`, `:61`) — the `q=−1` escape
  pole: a reading always leaves a residue outside its image. `self_covering_closure` (`:69`) bundles both
  (injective ∧ ¬surjective). The standard conjectures are the *optimistic* `q=+1` reading of this — "the
  factorization is faithful AND full, the realization loses nothing" — which the calculus's own theorem
  says holds on the faithful half (`object1_injective`) and **fails on the surjective half**
  (`object1_not_surjective`): the universal Lens covers everything injectively but is never onto. So the
  motivic-Galois / Tannakian structure is the `Aut` of the universal Lens read at the `q=+1` (converge)
  pole, and the conjecturality is precisely the `q=−1` (escape) residue that no realization captures.

## Re-seeing — ⟨C | L⟩

```
   category of motives          =  ⟨ Raw / the universal C (the cochain complex) | read universally ⟩
                                   =  the INITIAL object every reading is read out of  (raw_initial)
   a motive                     =  a piece of the universal C  (a Raw / a cochain class)
   Weil cohomology (realization) =  a reading L (a Lens) factoring through C  (view_factors_through_morphism)
   "every Weil cohomology factors uniquely through motives"
                                =  Lens.view = Raw.fold is the UNIQUE arrow out of Raw  (raw_initial / dhom_unique_pointwise)
   Betti / de Rham / ℓ-adic     =  three L's on ONE C  (the SAME motive read three ways)
                                   = homological_algebra.md's "homology/de Rham/sheaf = one machine", made universal
   comparison iso (Betti ≅ dR)  =  two readings with equal kernel  (lensIso_iff_kernel_eq)
   realization is a FUNCTOR      =  a Lens-morphism h with M.view = h ∘ L.view  (view_factors_through_morphism)
   motivic Galois group         =  Aut of the universal Lens  (the q=+1 Aut-invariant reading; det_holonomy_eq_one)
   Tate twist / weight          =  the fold-height grading of C  (isPart_wf, the well-founded degree)
   standard conjectures (faithful/full)
                                =  the q=±1 residue of the universal Lens read on itself:
                                   faithful  = object1_injective  (q=+1, distinct motives separated)
                                   full/total = object1_not_surjective FAILS  (q=−1, a residue always escapes)
   Tannakian structure          =  the universal Lens + its Aut groupoid  (LensIso, lensIso_iff_kernel_eq)
```

So **"category of motives", "Weil cohomology factors uniquely", "realization functor", and "comparison
isomorphism" are ONE statement** — the calculus's universal factorization `Lens.view = Raw.fold`
(`raw_initial`), instanced on the cohomology complex. Set against the field's named pieces:

| classical motivic object | = the 213 reading | already in calculus | Lean anchor |
|---|---|---|---|
| category of motives (universal target) | the universal `C` = `Raw`, the initial object | `category_theory.md` (`Raw` = initial), `yoneda.md` | `raw_initial` (`SemanticAtom.lean:412`) |
| "every Weil cohomology factors uniquely" | `Lens.view = Raw.fold` is the unique arrow out of `Raw` | the CORE theorem | `raw_initial`, `dhom_unique_pointwise` (`UniversalDistinguishing.lean:103`) |
| a realization (Betti/dR/ℓ-adic) = a functor out of motives | a reading `L` factoring through `C` | `homological_algebra.md` (one machine, three outputs) | `view_factors_through_morphism` (`Morphism.lean:37`) |
| realization is a functor (natural) | a Lens-morphism `h`: `M.view = h∘L.view` | `two_cells.md` (readings = 2-category) | `IsLensMorphism` (`Morphism.lean:29`), `refines_of_morphism` (`:60`) |
| comparison isomorphism (Betti ≅ dR/ℂ) | two readings, equal kernel | `equivalence.md`, `category_theory.md` | `lensIso_iff_kernel_eq` (`Unified.lean:64`), `LensIso` (`:42`) |
| motivic Galois group | `Aut` of the universal Lens (`q=+1` invariant) | `noether.md`, `representation.md`, `groups.md` | `det_holonomy_eq_one` (`HolonomyLattice.lean:136`); `LensIso` groupoid |
| Tate twist / weight grading | the fold-height of `C` | `dimension.md`, `homology.md` | `isPart_wf` (`Lambek.lean:199`) |
| standard conjectures: realization faithful | `q=+1`: distinct motives separated | `cardinality.md`, `topos.md` | `object1_injective` (`FlatOntologyClosure.lean:47`) |
| standard conjectures: realization full/total | `q=−1`: a residue always escapes (FAILS) | `cardinality.md`, `godel.md`, `measure.md` | `object1_not_surjective` (`:61`), `self_covering_closure` (`:69`) |

Motives consume the SAME apparatus the rest of the notebook runs on — *because* the field is asking the
calculus's own central question (which `C` does every reading factor through?) in cohomology's clothing.

## Revelation — motives = the calculus's OWN universal-factorization mechanism, named in cohomology

**Verdict: PREDICTION + the deepest REFLEXIVE consolidation. No new primitive — the most-built thing in
the whole repo (the Lens framework's universal property) IS the motivic idea.** Where
`homological_algebra.md` named the calculus's *residue-taking* half, this note names its
*universal-factorization* half. The named motivic objects (`Motive`, `WeilCohomology`, the realization
functors, `motivicGalois`, the Tannakian category) are **ABSENT** — grep-confirmed; the universal-property
MECHANISM they would package is the load-bearing core of the framework. Leg by leg, honest.

**(1) ★ The collapse: "motives = the universal cohomology every Weil cohomology factors through" IS
`raw_initial` (`Lens.view = Raw.fold` is the unique arrow out of `Raw`).** This is not an analogy chased
after the fact — it is the *same sentence*. Grothendieck: a motive is the universal target through which
every cohomology factors *uniquely*. The calculus: `Raw` is initial, so `Lens.view = Raw.fold` is the
**unique** distinguishing-preserving arrow `Raw → α` for every reading-target `α` (`raw_initial`,
`SemanticAtom.lean:412`, **PURE**; uniqueness pointwise to avoid `funext`). The pointwise uniqueness is
re-proved as `dhom_unique_pointwise` (`UniversalDistinguishing.lean:103`, **PURE, scanned 6/0**). So the
defining universal property of the category of motives is, term for term, the defining universal property
of `Raw`. The category of motives = the universal `C`; "factors uniquely" = initiality.

**(2) ★ Realizations = Lenses on one `C`, and the factorization is LITERAL.** "A realization is a functor
out of motives" = "a reading `L` factors through the universal `C`". The Lean statement
`view_factors_through_morphism` (`Morphism.lean:37`, **PURE, scanned 3/0**) reads
`M.view r = h (L.view r)` — a coarser realization `M` is a finer reading `L` post-composed with a
forgetful `h` (a Lens-morphism `IsLensMorphism`, `:29`). Betti, de Rham, ℓ-adic are three such `M`'s
factoring through one finer reading of the same motive `C`. This is the universal-statement form of
`homological_algebra.md`'s "homology / de Rham / sheaf are three outputs of one machine": there it was
three instances of `Residue(L,C)`; here it is three Lenses `L` on one universal `C`, factoring by the
naturality triangle. The comparison isomorphisms (Betti ≅ de Rham over ℂ) are kernel-equalities:
`lensIso_iff_kernel_eq` (`Unified.lean:64`) — two realizations are isomorphic iff they induce the same
kernel on `Raw`, i.e. identify the same motivic data. The realizations being *natural* (functorial) is
that readings form a **2-category** (`two_cells.md`): `refines_of_morphism` (`:60`) shows a 2-cell induces
a 1-cell — a realization-with-naturality induces a refinement.

**(3) ★ The motivic Galois group = the `Aut` of the universal Lens (`q=+1` invariant).** The motivic
Galois group is the automorphism group of the fiber/realization functor in the Tannakian story — the
symmetries that fix the realization. In the calculus that is the `Aut`-family of the universal Lens read
through the `q=+1` invariant character (`noether.md`/`representation.md`/`groups.md`): the conserved,
`Aut`-invariant readout. The closest built witness is `det_holonomy_eq_one` (`HolonomyLattice.lean:136`,
**PURE, scanned 26/0**) — the `q=+1` flatness/conservation invariant the notebook reads as the Noether
charge and the curvature-flatness condition; the motivic Galois group is that same `Aut`-invariant reading
on the universal Lens, with the groupoid structure `LensIso`/`lensIso_refl`/`lensIso_trans`
(`Unified.lean:42,46,54`). The Tate twist / weight is the fold-height grading of `C` (`isPart_wf`,
`Lambek.lean:199`, **PURE, scanned 22/0**) — the well-founded degree the calculus already carries
(`dimension.md`/`homology.md`).

**(4) ★ The standard conjectures = the `q=±1` residue of the universal Lens read on itself — and the
calculus SPLITS them honestly.** This is the genuine leverage, not a re-description. The standard
conjectures (and "numerical = homological equivalence", and "motives are Tannakian") amount to: the
universal factorization is **faithful and full** — no realization loses information, the universal `C` is
*reached* by the readings. The calculus's own self-cover theorem answers this with a split, and the split
is `q=±1`:
- **faithful (`q=+1`) — TRUE.** `object1_injective` (`FlatOntologyClosure.lean:47`, **PURE, scanned
  7/0**): the universal distinguishing is injective, distinct motives are genuinely separated, the
  realization records them. The optimistic half of the conjectures sits at the `q=+1` converging pole and
  *holds*.
- **full / total (`q=−1`) — the residue that ESCAPES.** `object1_not_surjective` (`:61`, PURE): the
  universal Lens is **never onto** — a reading always leaves a residue outside its image (the
  Cantor-diagonal `q=−1` escape, the same one underlying `cardinality.md`/`godel.md`/`measure.md`).
  `self_covering_closure` (`:69`) bundles both poles: injective ∧ ¬surjective.

So the calculus *predicts the shape of the conjecturality*: the realization is faithful (provable, `q=+1`)
but the demand that it be *total* (the surjective/"full" half) is the `q=−1` escape residue — exactly the
flavour of "open conjecture" the standard conjectures have. This is the residue tag `ResidueTag`
(`ResidueTag.lean`, **scanned 55/0**, `residue_tag_two_poles:228`, `multiplier_unimodular:86`) read on
the universal Lens: the motivic program lives at the `q=+1` faithful pole, the conjectures are the wager
that the `q=−1` half also closes.

**Honest boundary — built mechanism vs absent named object.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the **universal factorization** — `raw_initial`
  (`SemanticAtom.lean:412`), `dhom_unique_pointwise` (`UniversalDistinguishing.lean:103`, 6/0),
  `universalMorphism_unique` (`SemanticAtom.lean:388`); (b) the **realization-as-Lens factorization** —
  `view_factors_through_morphism` / `IsLensMorphism` / `refines_of_morphism` (`Morphism.lean:37,29,60`,
  3/0); (c) the **comparison-iso = kernel equality** — `lensIso_iff_kernel_eq` / `LensIso`
  (`Unified.lean:64,42`); (d) the **`q=±1` faithful/total split** — `object1_injective` /
  `object1_not_surjective` / `self_covering_closure` (`FlatOntologyClosure.lean:47,61,69`, 7/0), tagged by
  `ResidueTag` (`ResidueTag.lean`, 55/0); (e) the **`Aut`-invariant (`q=+1`) motivic-Galois reading** —
  `det_holonomy_eq_one` (`HolonomyLattice.lean:136`, 26/0); (f) the **weight/Tate-twist grading** —
  `isPart_wf` (`Lambek.lean:199`, 22/0); (g) the **cohomology complex the motive lives in** —
  `dsq_zero_universal_delta4` (`V4Capstone.lean:41`, 5/0), `reduced_betti_d4_contractible` /
  `betti_one_cycle` / `loopClass_not_coboundary` / `cycle_vs_contractible_qpm`
  (`NonzeroBetti.lean:111,134,173`; `BettiKernel.lean:63`, 56/0 + 11/0) — the `q=±1` realization residue
  in the cohomology setting, the literal `homological_algebra.md` machine.
- *Conceptual-only / the precise missing leg (the `homological_algebra.md`/`sheaf_theory.md`-style gap):
  the named MOTIVIC OBJECTS are ABSENT.* Grep over `lean/E213` for `Motive`/`motivic`/`WeilCohomology`/
  `realization`(as a motive-realization functor)/`motivicGalois`/`Chow`/`pureMotive`/`correspondence`(as
  a Chow correspondence)/`numericalEquiv` returns **zero motivic Lean declarations**. The `MotivicBridge`
  token in `Lib/Math.lean:161` is a **stale docstring** describing the Hodge-conjecture subtree — no such
  directory or file exists (the actual Hodge `Bridge/` contains statistical-physics bridges: `SpinGlass`,
  `MLDecoder`, `Ising`, not motives). There is **no** `Motive` type, **no** category of motives, **no**
  `WeilCohomology` interface, **no** realization functor `Mot → Vec`, **no** `motivicGalois`/Tannakian
  object, **no** Chow group / algebraic-correspondence object, **no** numerical/homological-equivalence
  comparison. This is the SAME shape as `homological_algebra.md`'s missing `Ext^n`/resolution object and
  `sheaf_theory.md`'s missing presheaf-bundle: the *universal-factorization mechanism* (`raw_initial`,
  `view_factors_through_morphism`), the *realization-as-Lens* (`lensIso_iff_kernel_eq`), the *`Aut`/Galois
  invariant* (`det_holonomy_eq_one`, `LensIso`), the *weight grading* (`isPart_wf`), and the
  *faithful/total `q=±1` split* (`object1_injective`/`object1_not_surjective`) are each built and PURE; the
  **named motivic objects that would weld them** are the located open legs.

So: **PREDICTION on the consolidation (a motive = the calculus's universal Lens; the category of motives =
the universal `C`/`Raw`; "every Weil cohomology factors uniquely" = `raw_initial`/`dhom_unique_pointwise`;
realizations Betti/dR/ℓ-adic = Lenses on one `C` factoring by `view_factors_through_morphism`; the motivic
Galois group = `Aut` of the universal Lens; the Tate twist = the fold-height grading; the standard
conjectures = the `q=±1` faithful/total split of the universal Lens on itself), cashed at the
universal-property / factorization / `q=±1`-split level; PARTIAL because the `Motive`/`WeilCohomology`/
realization/`motivicGalois`/Chow OBJECTS are absent — the named open legs, not hand-waves.**

This passes the re-skin guard at the deepest reflexive level the notebook has reached: it does not
re-describe motives — it **identifies the motivic universal property with the calculus's OWN central
theorem** (`Lens.view = Raw.fold`, `raw_initial`), the most-reused and most-built object in the entire
repo, grounded by the *same* PURE universal-factorization (`view_factors_through_morphism`,
`dhom_unique_pointwise`) and the *same* `q=±1` faithful/total split (`object1_injective` /
`object1_not_surjective`) that certify `category_theory.md`, `yoneda.md`, and `homological_algebra.md`.

## Revelation summary (collapse + forcing + the reflexive spine)

**Collapse — "universal cohomology", "realization functor", "comparison isomorphism", and "factors
uniquely" are ONE statement: the calculus's universal factorization `Lens.view = Raw.fold`.** Grothendieck
built motives to be the single object every cohomology reads out of, uniquely; the calculus built `Raw` to
be the single object every reading reads out of, uniquely (`raw_initial`). The realizations Betti / de Rham
/ ℓ-adic are the SAME `C` read by three Lenses, factoring through the universal reading
(`view_factors_through_morphism`) — the universal-statement form of `homological_algebra.md`'s "three
outputs of one machine". The single forcing sentence, read at both poles:

- **`q=+1` (the faithful pole = the realization records the motive = the standard conjectures' optimistic
  half).** The universal Lens is **injective** (`object1_injective`): distinct motives are genuinely
  separated, distinct cohomology classes have distinct realizations. This is the converging/closure pole
  (`converge`, `det_holonomy_eq_one` the `Aut`-invariant), where the motivic Galois group lives and where
  the standard conjectures' faithfulness holds — provably.
- **`q=−1` (the total pole = the residue no realization captures = the conjecturality).** The universal
  Lens is **never surjective** (`object1_not_surjective`): a residue always escapes every reading's image,
  the Cantor-diagonal `q=−1` escape shared with `cardinality.md`/`godel.md`/`measure.md`. The demand that
  the realization be *total* (the "full" half of the standard conjectures, "every Hodge/motivic class is
  captured") is exactly this escape residue — which is why it is conjectural rather than provable.

**The reflexive spine:** the decomposition cluster's two deepest reflexive entries are now the two halves
of the README normal form. `homological_algebra.md` named the **`Residue(L,C)`** half — the residue-taking
operation, graded by degree. **`motives.md` names the `⟨C|L⟩` half** — the universal factorization, which
universal `C` every reading `L` passes through. Motives = `⟨C|L⟩` (the universal `C` + its realizations
`L`); homological algebra = `⊕ Residue(L,C)` (what each realization leaves). Together they say the README
normal form `⟨C|L⟩ ⊕ Residue(L,C)` is not a description of motivic cohomology but its **mechanism**:
a motive is a piece of the universal `C`, a realization is a reading `L` factoring through it, the standard
conjectures are the `q=±1` residue of that factorization read on itself. **EXTEND by reflexive
consolidation; no new axis; interior model v7.1 holds.** The one genuine absence — the
`Motive`/`WeilCohomology`/realization/`motivicGalois`/Chow object — is located precisely: the universal-Lens
twin of `homological_algebra.md`'s missing `Ext^n` object and `sheaf_theory.md`'s missing presheaf-bundle,
the named motivic object that would weld the (all-built) universal-factorization mechanism into a category
of motives with realization functors.

## Note for the technique

**No new primitive; the deepest reflexive consolidation — motives are the calculus's universal-factorization
mechanism (`Lens.view = Raw.fold`), NAMED in cohomology.** It does not extend model v7.1; it *names the
core theorem the framework is built on* (`raw_initial`, the universal property of `Raw`):
- the **universal `C`** (the category of motives) is `Raw`, the initial object every reading reads out of;
- the **realizations** (Betti/dR/ℓ-adic) are readings `L` factoring through `C` (`view_factors_through_morphism`),
  the same `C` read three ways — `homological_algebra.md`'s "one machine, three outputs" made universal;
- the **`q=±1` faithful/total split** (`object1_injective`/`object1_not_surjective`) supplies the standard
  conjectures: faithful at `q=+1` (provable), total at `q=−1` (the escape residue, conjectural);
- the **`Aut` of the universal Lens** (`det_holonomy_eq_one`, `LensIso`) is the motivic Galois group; the
  **fold-height** (`isPart_wf`) is the weight / Tate-twist grading.

The lesson for the model: motives are the field where the calculus **recognizes its own engine**. The two
reflexive entries are the two halves of the normal form — `homological_algebra.md` = `Residue(L,C)` (the
residue operation), `motives.md` = `⟨C|L⟩` (the universal factorization). This is the sharpest confirmation
that the README's normal form is an *operation*, not a description: motivic cohomology is the discipline
whose entire content is "factor every cohomology through one universal `C`", which is the calculus's
`raw_initial` performed on cohomology complexes. The one genuine absence — the `Motive`/`WeilCohomology`/
realization/`motivicGalois`/Chow object — is located precisely: every leg it would need *structurally* (the
universal factorization, the realization-as-Lens, the comparison-iso = kernel-equality, the `Aut`/Galois
invariant, the weight grading, the faithful/total `q=±1` split) is present and PURE; only the named motivic
object is open.

---

## Verified Lean anchors (file:line — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| **★ category of motives = universal `C`; "factors uniquely" = `Lens.view=Raw.fold` initiality** | `Lens/Foundations/SemanticAtom.lean:412 raw_initial`, `:388 universalMorphism_unique`; `Lens/Foundations/UniversalDistinguishing.lean:103 dhom_unique_pointwise` | ∅-axiom PURE ✓ (`raw_initial`/`universalMorphism_unique` PURE within mixed module; UnivDist scanned **6/0**) |
| `Lens.view` = the catamorphism `Raw.fold` (the read-out) | `Lens/LensCore.lean:42 Lens.view` (`r.fold L.base_a L.base_b L.combine`) | ∅-axiom PURE ✓ |
| **★ realization = a Lens factoring through `C` (the realization-functor naturality triangle)** | `Lens/Compose/Morphism.lean:37 view_factors_through_morphism`, `:29 IsLensMorphism`, `:60 refines_of_morphism` | **PURE, scanned 3/0** ✓ |
| comparison iso (Betti ≅ dR) = two readings, equal kernel | `Lens/Unified.lean:64 lensIso_iff_kernel_eq`, `:42 LensIso`, `:46 lensIso_refl`, `:54 lensIso_trans` | ∅-axiom PURE ✓ |
| `Lens.refines` (the reading order / a coarser realization) | `Lens/LensCore.lean:90 Lens.refines` | ∅-axiom PURE ✓ |
| **★ standard conjectures: faithful (`q=+1`, TRUE) / total (`q=−1`, escapes)** | `Lens/Foundations/FlatOntologyClosure.lean:47 object1_injective`, `:61 object1_not_surjective`, `:69 self_covering_closure` | **PURE, scanned 7/0** ✓ |
| the `q=±1` residue tag (the conjecturality's two poles) | `Lib/Math/Foundations/ResidueTag.lean:228 residue_tag_two_poles`, `:86 multiplier_unimodular`, `:73 ResidueTag` | **PURE, scanned 55/0** ✓ |
| motivic Galois group = `Aut`-invariant (`q=+1`) reading of the universal Lens | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:136 det_holonomy_eq_one` | **PURE, scanned 26/0** ✓ |
| Tate twist / weight = the fold-height grading of `C` | `Theory/Raw/Lambek.lean:199 isPart_wf` | **PURE, scanned 22/0** ✓ |
| the cohomology complex the motive lives in (`δ²=0`, the realization residue) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4`; `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible`; `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:111 betti_one_cycle`, `:134 loopClass_not_coboundary`, `:173 cycle_vs_contractible_qpm` | **PURE, scanned V4Capstone 5/0, BettiKernel 11/0, NonzeroBetti 56/0** ✓ |
| cross-frame | `homological_algebra.md` (`Residue(L,C)` graded — the other half of the normal form), `category_theory.md` (`Raw` = initial), `yoneda.md` (`self_covering_closure` = Yoneda ⊕ residue), `de_rham.md`/`sheaf_theory.md`/`homology.md` (the realizations as one machine), `representation.md`/`noether.md` (the `Aut`-invariant character), `cardinality.md`/`godel.md`/`measure.md` (the `q=−1` escape) | prior, ∅-axiom ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py` from repo root):**
- `E213.Lens.Foundations.UniversalDistinguishing` — **6 pure / 0 dirty** (`dhom_unique_pointwise` PURE).
- `E213.Lens.Compose.Morphism` — **3 pure / 0 dirty** (`view_factors_through_morphism`,
  `IsLensMorphism`, `refines_of_morphism` all PURE).
- `E213.Lens.Foundations.FlatOntologyClosure` — **7 pure / 0 dirty** (`object1_injective`,
  `object1_not_surjective`, `self_covering_closure` all PURE).
- `E213.Lib.Math.Foundations.ResidueTag` — **55 pure / 0 dirty**.
- `E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice` — **26 pure / 0 dirty**
  (`det_holonomy_eq_one` PURE).
- `E213.Theory.Raw.Lambek` — **22 pure / 0 dirty** (`isPart_wf` PURE).
- `E213.Lib.Math.Cohomology.Examples.BettiKernel` — **11 pure / 0 dirty**;
  `E213.Lib.Math.Cohomology.Delta.V4Capstone` — **5 pure / 0 dirty**;
  `E213.Lib.Math.Cohomology.Examples.NonzeroBetti` — **56 pure / 0 dirty**.
- `E213.Lens.Foundations.SemanticAtom` — module is **11 pure / 23 dirty** overall, BUT the cited
  `raw_initial` and `universalMorphism_unique` are individually **PURE** (the DIRTY entries are only the
  `canonical{Truth,Or,Iff}Map` classical-correspondence surface that uses `propext`, not the
  universal-property theorems — the PURE/DIRTY = Heyting/Boolean line of `topos.md`).

## Dropped / flagged

- **`Motive` / `motivicCohomology` / `WeilCohomology` / realization functor / `motivicGalois` / Chow /
  `pureMotive` / algebraic-correspondence / numerical-equivalence OBJECTS — ABSENT, located (predicted).**
  Grep over `lean/E213` (case-insensitive) for `Motive`/`motivic`/`WeilCohomology`/`realization`(as a
  motive functor)/`motivicGalois`/`Chow`/`pureMotive`/`correspondence`(as Chow)/`numericalEquiv` returns
  **zero motivic Lean declarations**. The only `Motive`-shaped tokens are (a) `Reach.lean:62` `motive :=`
  — Lean's eliminator `motive` keyword, unrelated; (b) `Lib/Math.lean:161` `MotivicBridge` — a **stale
  docstring** naming a non-existent Hodge subdirectory (no `MotivicBridge` dir/file exists; the actual
  Hodge `Bridge/` holds `SpinGlass`/`MLDecoder`/`Ising`/`Potts` statistical-physics bridges). Flagged as a
  candidate doc-fix for an org-audit pass; NOT cited as a motives anchor. This is the precise missing leg —
  the universal-Lens twin of `homological_algebra.md`'s missing `Ext^n` and `sheaf_theory.md`'s missing
  presheaf-bundle.
- **The Tannakian category / fiber-functor-with-`⊗` object — ABSENT.** The `Aut`-groupoid (`LensIso`) and
  the `⊗`-flavour reading (`ConvolveProfile`, cited in `homological_algebra.md`) are built, but no
  `TannakianCategory`/`fiberFunctor`/`neutralTannakian` object that would package the motivic Galois group
  as the `Aut` of a tensor-functor. Conceptual at the object level; the `Aut`-invariant reading
  (`det_holonomy_eq_one`) and the groupoid (`lensIso_*`) are built.
- **No verified buildable witness proposed.** Unlike `homological_algebra.md` (which named the nonzero-`H¹`
  witness, now built as `NonzeroBetti.lean`), this note's content is the *identification* of the motivic
  universal property with `raw_initial` — already a closed PURE theorem. A buildable next step would be a
  named `Realization := Lens` wrapper with `view_factors_through_morphism` re-exported as
  "every realization factors through the universal motive `Raw`", but it would only re-package the
  already-PURE `view_factors_through_morphism` / `raw_initial` — not asserted here as a decide-witness, and
  not claimed built.
