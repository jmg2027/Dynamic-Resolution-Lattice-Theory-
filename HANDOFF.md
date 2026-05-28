# Session handoff

Branch: `claude/gra-promotion-essay-LwwoA` — GRA Phases 1–22 closed
(401 PURE / 0 DIRTY).

## This session — Phase 22: Lens.Unified × GRA capstone (401 PURE)

One new file extending GRA from 27 → 28 files, 374 → 401 PURE.

  · **Phase 22 `LensIsoCapstone.lean`** (27 PURE) — the deepest
    213-native statement of GRA's content.  Connects GRA's
    canonicalGradeMap (Phase 16) and its universal property
    (Phase 18) to `Lens.Unified.LensIso` (the 213-native
    equivalence concept on Lenses).
      · `gradeLens : Lens Nat := ⟨2, 3, (· + ·)⟩` is the
        canonical 213 Lens.  `gradeLens.view r = Raw.fold 2 3
        (· + ·) r = canonicalGradeMap r` by definitional
        unfolding.
      · `profile_view_eq_canonical` lifts Phase 18 to Lens
        vocabulary.
      · `profile_lens_LensIso_gradeLens` — **the headline**:
        every (2, 3)-profile Lens on Nat is `LensIso` to
        `gradeLens`.  Proof via `Lens.Unified.lensIso_iff_kernel_eq`.
      · `walkLens` / `cochainLens` / `truncationLens` /
        `operadLens` / `resolutionLens` — five Reading Lens
        defs (definitionally `gradeLens`); each `*Lens_LensIso`
        theorem confirms membership.
      · `*Realize_grade_eq_lens` (five) — Phase 17 realizations
        project to `gradeLens.view` by `rfl`.
      · `gra_lens_iso_class_capstone_holds` — the bundle of
        universal property + 5 Reading `LensIso`s.

The (2, 3)-arithmetic forced by atomic distinguishing IS the
`LensIso` equivalence class of `gradeLens` — the strongest
formal statement of GRA's relation to Raw.  All five Readings
are explicit class members; the universal property forces any
future (2, 3)-Reading into the same class.

## Previous step — Phase 21: full HasDistinguishingWFull on GRA23 (374 PURE)

One new file extending GRA from 26 → 27 files, 362 → 374 PURE.

  · **Phase 21 `HasDistinguishingWFull.lean`** (12 PURE) — closes
    the categorical-distinctness leg of the Cat-as-Reading
    frontier.
      · `HasDistinguishingWFull.{u, v}` — extends Phase 20's
        `HasDistinguishingW` with `distinct_equiv : Equiv a b →
        False`.  Type-valued because `Equiv` is Type-valued.
      · `trivial23_not_iso_NT` — **the headline cardinality
        proof**.  Any would-be `GRAIso trivial23 GRA23_NT` gives
        `iso.invFun : Nat → TrivialCarrier`, but `TrivialCarrier`
        is a subsingleton (proved by `cases x; cases y; rfl`),
        so `iso.invFun 0 = iso.invFun 1`.  `right_inv` then
        forces `0 = iso.toFun (iso.invFun 1) = 1`, contradicting
        `decide 0 ≠ 1`.
      · `gra23HasDistinguishingWFull : HasDistinguishingWFull.{1, 1}
        GRA23` — the full instance.  Atoms `trivial23` (1-element
        carrier) and `GRA23_NT` (Nat carrier); combine =
        `Monoidal.product`; Equiv = `GRAIso` on underlying
        models; refl/symm/trans from Phase 7; combine_sym from
        Phase 20's `productSwapIso`; distinct_equiv from the
        cardinality proof.
      · `hasDistinguishingWFull_witness` — `Nonempty` existence
        statement.

The categorical "Cat-as-Reading of GRA" content is now a full
Lean theorem at `Type 1`: there exists a categorically-distinct
HasDistinguishingW structure on a `Type 1` carrier with natural
combine, iso-symmetric combine_sym, and categorical
distinctness.  The Phase 17/18/19/20/21 chain closes every leg
of the essay's frontier.

PURE: uses only `cases` on TrivialCarrier (the structural
subsingleton fact), iso's `right_inv` axiom (definitional),
and `decide` on Nat literal inequality.  No propext, no
Classical, no Mathlib.

## Previous step — Phase 20: iso-symmetric natural combine_sym (362 PURE)

One new file extending GRA from 25 → 26 files, 357 → 362 PURE.

  · **Phase 20 `HasDistinguishingW.lean`** (5 PURE) — the natural
    iso-symmetric combine question that Phase 19's strict
    combine could not capture.
      · `HasDistinguishingW.{u, v}` typeclass — like Phase 19's
        `HasDistinguishingU` but with `combine_sym` taking values
        in a `Sort v`-valued `Equiv` relation instead of strict
        `=`.  Refl/symm/trans of `Equiv` are required.
      · `productSwapIso` — the headline construction.  For any
        two (2, 3)-GRA models `M₁`, `M₂` (with the parameter
        hypotheses), gives a `GRAIso` between
        `Monoidal.product M₁ M₂` and `Monoidal.product M₂ M₁`.
        Underlying map is pair-swap `(a, b) ↦ (b, a)`.
        `grade_comm` discharges by `Nat.add_comm`;
        `oplus_comm`/`otimes_comm` by `cases p; cases q; rfl`.
      · `product_combine_sym_witness` — packages the swap iso
        as the witness "monoidal product is iso-symmetric".
      · `productSwapIso_involutive` — swap is self-inverse at
        the function level.
      · `product_grade_sym` — additive grade symmetry.
      · `product_combine_sym_at` — the swap iso restated as
        the combine_sym component of a `HasDistinguishingW`
        instance.
  · Combined with Phase 7's `GRACat` and Phase 15's
    `Monoidal.product`, this completes `GRACat` as a *symmetric
    monoidal category* with `productSwapIso` as the braiding.

Essay updated: Phase 20 closes the natural-combine question
("natural combine on Cat-objects is iso-symmetric, not strict").
The two-phase pair (Phase 19 strict + Phase 20 weak) covers
both the universe-lifting existence demonstration and the
natural-combine content question.

## Previous step — Phase 19: strict 2-cat universe-lifting (357 PURE)

One new file extending GRA from 24 → 25 files, 342 → 357 PURE.

  · **Phase 19 `Universe1.lean`** (15 PURE) — the strict
    2-categorical universe-lifting frontier from Phase 18.
      · `HasDistinguishingU.{u}` — universe-polymorphic parallel
        of `Lens.SemanticAtom.HasDistinguishing` (which is fixed
        at `Type 0`).
      · `Reading` enum (from Phase 7) is enriched with `deriving
        DecidableEq` so strict-equality tests work PURE.
      · `readingCombine r s := if r = s then r else .NT` is
        strictly commutative (the condition `r = s` is symmetric;
        proof closes by `by_cases`).
      · `readingHasDistinguishingU : HasDistinguishingU.{0} Reading`
        — instance at `Type 0` with atoms `NT`, `Graph` and the
        strict-commutative combine.
      · `liftedReadingHasDistinguishingU : HasDistinguishingU.{1}
        (ULift.{1, 0} Reading)` — **the strict 2-cat statement**:
        a `Type 1` carrier admits the distinguishing structure.
        Lifts atoms via `ULift.up` and combine via
        `liftedCombine r s := ULift.up (readingCombine r.down
        s.down)`.
      · `reading_atomic_agreement` — the lifted carrier's atomic
        grade map matches `canonicalGradeMap` at `Raw.a` and
        `Raw.b` (both `rfl`), so the (2, 3)-profile is preserved.
      · `universe1_distinguishing_witness` — the capstone
        delivering the `Type 1` instance.
  · This meets the strict 2-categorical universe-lifting
    requirement Phase 18 named.  The `Type 1` carrier exists
    with the distinguishing structure; the parameterless
    arithmetic discipline is not broken by universe lifting.

Essay updated: open frontier shifts from "strict 2-cat" (closed)
to "natural-combine on Cat-objects requires iso-symmetric
combine_sym, a weakening of `HasDistinguishingU`" — the
*content* of "Cat-Lens" beyond Phase 19's universe-lifting
demonstration.

## Previous step — Phase 18: universal property, 1-cat proxy for GRACat-as-Cat (342 PURE)

One new file extending GRA from 23 → 24 files, 329 → 342 PURE.

  · **Phase 18 `Universality23.lean`** (13 PURE) — the parameterless
    forcing statement at the Raw level.
      · `canonicalGradeMap_universal` — any `f : Raw → Nat` with
        `f Raw.a = 2`, `f Raw.b = 3`, slash-additive equals
        `canonicalGradeMap` pointwise.  Proof: Raw induction.
      · Specialised: each enrichment's grade map (`walkGradeMap`,
        `cochainGradeMap`, `truncationGradeMap`, `operadGradeMap`,
        `resolutionGradeMap`) is derived as an instance of the
        universal property — `*_forced` theorems.
      · Realization-level forcing: `walkRealize_grade_forced` etc.
      · `two_atoms_slash_agree` — two such functions agree pointwise.
      · Capstone `canonical_arithmetic_forced` — the parameterless
        forcing statement.
  · This is the 1-categorical proxy for the essay's "GRACat-as-Cat
    is a Reading" frontier.  The strict 2-categorical statement
    requires `HasDistinguishing` on `Cat`-objects, which needs
    universe lifting — outside the parameterless-arithmetic
    discipline.  The universal property captures the conceptual
    content: ANY structure (Cat-object included) whose grade map
    satisfies the (2, 3)-profile is forced to read the canonical
    arithmetic.

Essay updated: "Open beyond Phase 18" section names the strict
2-categorical statement as the remaining open question, with the
explanation that the 1-categorical content has been captured.

## Previous step — Phase 17: carrier realization, closes Phase 16 frontier (329 PURE)

One new file extending GRA from 22 → 23 files, 296 → 329 PURE.

  · **Phase 17 `CarrierRealization.lean`** (33 PURE) — closes the
    open frontier named in
    `theory/essays/gra_as_substrate_of_cat_hott.md` (the carrier-
    level Lens equation between enrichments).  Key lemma
    `canonical_ge_2 : ∀ r : Raw, canonicalGradeMap r ≥ 2` (Raw
    induction: atoms → 2 or 3, slash → sum of ≥-2 values ≥ 4)
    enables direct construction
    `walkRealize r := ⟨canonicalGradeMap r, Or.inr (canonical_ge_2 r)⟩`
    (and the same shape for cochainRealize / truncationRealize /
    operadRealize / resolutionRealize).  This *bypasses* the
    enriched `Raw.fold` route — no `combine_sym` proof needed
    for the Prop-field-carrying carriers (which would force
    structural equality with `propext`).
  · Each realization's grade-projection equals `canonicalGradeMap`
    by `rfl`; all pairwise carrier-level agreement theorems
    (including the headline `truncation_operad_realize_agree`,
    the HoTT ↔ Higher Algebra equation at the carrier level)
    follow by `rfl`.
  · Atom and slash behavior at the carrier level: `*_realize_a`,
    `*_realize_b`, `*_realize_slash` for all five realizations.

The essay's open frontier section was rewritten to mark this
closure, with a brief explanation of the bypass strategy.

## Previous step — Phase 16: Lens bridge + essay (296 PURE)

One new file + one new essay extending GRA from 21 → 22 files,
259 → 296 PURE:

  · **Essay `theory/essays/gra_as_substrate_of_cat_hott.md`** —
    "Could GRA play the role Category theory / HoTT normally
    occupy, but from a more fundamental position?"  The (2, 3)
    arithmetic is parameter-forced by atomic distinguishing;
    Cat and HoTT carry external design choices (universe, ∞-cat
    doctrine).  Hence the forcing direction is GRA → Cat/HoTT,
    not Cat/HoTT → GRA.  Companion to
    `gra_universality_one_principle.md`.
  · **Phase 16 `LensBridge.lean`** (37 PURE) — the canonical
    Raw-level grade map `canonicalGradeMap := Raw.fold 2 3 (· + ·)`,
    the PURE backbone of "(2, 3)-arithmetic at the Raw level".
    All five enrichment grade maps (walk / cochain / truncation
    / operad / resolution) are *definitionally* equal to
    `canonicalGradeMap`, so pairwise agreement theorems are `rfl`.
    Headline theorem `truncation_operad_grade_agree` proves the
    HoTT ↔ Higher Algebra Lens-level equation — they project to
    the same Raw-level kernel, hence are one Reading under
    different vocabularies.  Carrier-level `*_realize_a` /
    `_b` theorems show that the enriched `Raw.fold` (e.g.,
    `Raw.fold EdgeWalk.two EdgeWalk.three EdgeWalk.concat`)
    projects to the canonical value on atoms.

Avoids `HasDistinguishing`-typeclass plumbing (which would bring
`propext`); the literal Nat-level `Raw.fold 2 3 (· + ·)` with
`Nat.add_comm` discharging `Raw.fold_slash`'s combine-symmetry
hypothesis is PURE.

Tracking:
  · `lake build E213.Lib.Math.GRA` — 49/49 modules clean.
  · `tools/scan_axioms.py` — 296 PURE / 0 DIRTY (with 13
    additional HigherAlgebra decls verified PURE via direct
    `#print axioms`).

## Previous step — Phases 12–15 (259 PURE / 0 DIRTY)

7 new files extending GRA from 14 → 21 files, 167 → 259 PURE:

  · **Phase 12 (4 files)** — full carrier enrichment for the
    remaining 4 Readings (R₁/R₂/R₃/R₅), each parallel to
    `WalkEnrichment` (R₄):
      · `CochainEnrichment.lean` (12 PURE) — `Cochain` with
        degree constraint; cup-product `cup` and `tensor`;
        `GRA23_CochainEnriched` instance + `forgetHom`.
      · `HoTTEnrichment.lean` (12 PURE) — `Truncation`
        carrying homotopy level; suspension `Σⁿ` and smash `∧`;
        `GRA23_TruncationEnriched` + `forgetHom`.
      · `HigherAlgebraEnrichment.lean` (12 PURE) — `Operad`
        carrying `E_n` level; Day convolution + nested
        integration; `GRA23_OperadEnriched` + `forgetHom`.
      · `AnalysisEnrichment.lean` (12 PURE) — `Resolution`
        carrying analytic exponent; modulus composition +
        polynomial-depth product; `GRA23_ResolutionEnriched`
        + `forgetHom`.
  · **Phase 13 `Naturality.lean`** (13 PURE) — translation
    between enrichments is natural with respect to the
    forgetfuls.  Per-Reading `*_depth_natural` theorems +
    `DepthNaturality` capstone bundle.  `walk_cochain_*`
    theorems show cross-Reading translation via the hub.
  · **Phase 14 `SectionRetraction.lean`** (17 PURE) — each
    forgetful has a `Nat → Enriched` section on the valid
    image (`n = 0 ∨ n ≥ 2`).  `forget ∘ section = id`
    (retraction) and `section ∘ forget = id` (section
    identity) for all 5 enrichments.  `WalkRetract` packages
    the data.
  · **Phase 15 `Monoidal.lean`** (14 PURE) — `product :
    GRAModel → GRAModel → GRAModel` is the (2, 3)-monoidal
    product with component-wise `⊕`/`⊗` and additive grade.
    `trivial23` is the unit (one-element carrier, grade ≡ 0).
    `leftUnitHom`/`rightUnitHom` are the unit `GRAHom`s.

Tracking:
  · `lake build E213.Lib.Math.GRA` — 27/27 modules clean.
  · `tools/scan_axioms.py` — 259 PURE / 0 DIRTY total (with
    13 additional HigherAlgebra decls mis-attributed by the
    scanner's last-namespace heuristic but verified PURE by
    direct `#print axioms`).

## Previous step — Phases 7–11: category + enrichment (167 PURE)

5 new files extending GRA beyond the original Marathon 16 closure:

  · **Phase 7 `Category.lean`** (9 PURE) — 213-native
    universe-polymorphic `Cat` typeclass; `GRACat` for all GRA
    models; `Reading` enumeration of the 6 closed (2,3)-models;
    `ReadingCat` sub-category; `ReadingCat_connected` witness
    that every pair of Readings is related by a hub-and-spoke iso.
  · **Phase 8 `Groupoid.lean`** (10 PURE) — `Groupoid` typeclass
    sitting on top of `Cat`; pointwise `HEq`-form of "every
    `Reading.iso r s` is the identity at the carrier level" (the
    `HEq` form is forced because abstract `r.toModel.Carrier` and
    `s.toModel.Carrier` are syntactically distinct even though
    both reduce to `Nat`); `ConnectedHub` structure with
    `Reading.hubAtNT` as the concrete hub-and-spoke witness.
  · **Phase 9 `Hom.lean`** (10 PURE) — `GRAHom` (general
    structure-preserving map, not necessarily invertible);
    `id`/`comp` category laws; forgetful `GRAIso → GRAHom`
    (`isoToHom`) functoriality (refl/trans preservation);
    grade-agreement (`GRAHom.grade_agree`) and
    grade-oplus-via-hom (`GRAHom.grade_oplus_via`).
  · **Phase 10 `DepthFunctor.lean`** (9 PURE) — `GRA23` structure
    packaging the (2, 3)-parameter constraint; `GRA23.depth_const`
    showing all (2, 3)-models agree on depth; `readingToGRA23`
    upgrading each `Reading` enum to `GRA23`;
    `Reading_depth_const` as the capstone "depth is the unique
    structural invariant" claim.
  · **Phase 11 `WalkEnrichment.lean`** (12 PURE) — concrete
    carrier enrichment for R₄: `EdgeWalk` with
    `length = 0 ∨ length ≥ 2` bipartite constraint;
    `concat`/`tensor` operations; `GRA23_EdgeWalk` instance;
    `forgetHom` exhibiting the simplified `GRA23_Graph` as the
    image of `EdgeWalk` under the forgetful functor.

Total **167 PURE / 0 DIRTY** across all 14 files of `Lib/Math/GRA/`.

## Previous step — GRA full clear (Marathon 16 → 118 PURE / 0 DIRTY)

  · **Tier 5.1 cleared**: all `Lib/Math/GRA/` theorems are now
    STRICT ∅-axiom PURE.  Pattern:
      · switch `GRAModel.ax_coprime` from `Nat.gcd` (DIRTY via
        well-founded recursion) to `gcd213` (kernel-reducible)
      · introduce `GRA/Common.lean` with shared PURE Nat lemmas
        (`coprime_2_3`, `reach_23`, `depth_formula`, `ceil3_le_ceil2`,
        + `div3_3k_{1,2,3,4}` building blocks)
      · per-Reading proofs collapse to `rfl` / `Nat.le.refl` /
        delegation to Common
      · Translation theorems use Common helpers + explicit
        `Nat.add_le_add_left` / `Meta.Nat.NatDiv213.div_mul_le_self`
        / `Meta.Nat.AddMod213.div_add_mod` chains
      · No `omega`, no `simp [...]`, no Mathlib, no `Classical`.
  · Updated `STRICT_ZERO_AXIOM.md` Tier 5.1 from "backlog" to
    "CLEARED" with the upgrade pattern catalog.
  · Updated `theory/math/gra_book.md` + `graded_residue_arithmetic.md`
    + GRA umbrella docstring + `theory/math/graded_residue_arithmetic.md`
    file listing to reflect PURE status and add `Common.lean`.

### Math umbrella fixes (separate, prior commit)

7 pre-existing build failures in `Lib/Math` fixed:
`Extras` (unterminated docstring), `DyadicFSM/Pell/ProperMod`
(missing `ArithFSM` open), `ParadigmDomainGradedRing`
(`binom_5_row_sum` → `binom_5_row` rename), `ModArith/JoinEquivGCD`
(orphan `(gcd213_self ...)` fragments + missing `succ_sub_self_213`
in open), `AngleStructure/RotationOrder` (re-added
`angle_level{0,1,2}` projections), `CayleyDickson/Levels/Cayley`
(misplaced `open Cayley`), `Cauchy/Wallis` (orphan partial open).
Full `lake build` now 985/985 clean.

## Previous step — GRA promotion + essay (same session)

  · **Promotion**:
      · Created umbrella `lean/E213/Lib/Math/GRA.lean` and wired it
        into `lean/E213/Lib/Math.lean`.
      · Fixed pre-existing build failures in Marathon 16 code
        (omega could not bridge `(n+2)/3` vs `n/3 + (if n%3=0 then
        0 else 1)` without case-splitting on `n % 3 = 0`; affected
        6 files: `NumberTheory`, `Graph`, `Analysis`, `Cohomology`,
        `HoTT`, `HigherAlgebra`, `Translation`).
      · Added `hgen1`/`hgen2` hypotheses to
        `Translation.transport_depth_bound` (lemma was under-
        determined without gen2 equality).
      · Fixed simp-collapse on `master_translation*` (P((n+2)/3)
        repeated collapses to single P-application via and_self).
      · Marked `theory/math/gra_book.md` + `theory/math/graded_
        residue_arithmetic.md` as **CLOSED** (Marathon 16).
      · Added GRA entry to `lean/E213/ARCHITECTURE.md` Lib/Math/.
      · Added Tier 5.1 backlog entry to `STRICT_ZERO_AXIOM.md`
        for `Lib/Math/GRA/`'s ~67 `[propext, Quot.sound]`
        DIRTY theorems (mechanical omega→decide upgrade path).
      · Archived G148 / G150 / G151 to `research-notes/archive/`.
  · **Essay**: `theory/essays/gra_universality_one_principle.md`
    — "Walk-length, cup-length, truncation, chromatic height,
    resolution exponent — why are these the same?"  Derives
    answer via the `GRA23_*` instances + the master translation
    + the universal depth comparison; cross-frame with det(P)=1
    + Frobenius=1 + K_{3,2}^{(c=2)} closure form; honest open
    frontier (carrier-enrichment Phase 7).

## Previous session — GRA Universality Phase 6 COMPLETE (MARATHON DONE)

### Phase 6: Translation Theorems (ALL DONE)

  · `Translation.lean` — 9 sections, ~250 lines, 0 sorry
  · **T1 (R₄→R₁)**: `graph_distance_implies_cup_length`
    Walk-length depth = cup-length depth (identical formulas)
  · **T2 (R₅→R₃)**: `resolution_depth_implies_cell_count`
    Modulus composition depth = homotopy cell-count
  · **T3 (R₁→R₅)**: `cup_grade_is_resolution_compose`
    Cup-grade sum = resolution shift composition
  · **T4 (Prediction)**: `universal_depth_comparison`
    ⌈n/3⌉ ≤ (n+1)/2 — greedy on gen2 always beats naive gen1
    Novel result valid simultaneously in all 5 Readings
  · **Master Translation**: `master_translation_from_any`
    Any P((n+2)/3) implies P holds for all 5 depth functions
  · **Capstone**: `GRA_TranslationProgramme` + `gra_translation_witness`
    All translation results bundled

### Previous session — Phases 1–5

  · `GRAModel.lean`: typeclass + GRAIso refl/symm/trans
  · 5 Reading instances: NT, Graph, Analysis, Cohomology, HoTT, HigherAlgebra
  · `GRA_Universality` + `gra_universality_witness`: all pairwise iso
  · Hub-and-spoke architecture (NT hub, transitivity for all pairs)

## ★ GRA MARATHON STATUS: COMPLETE ★

All 6 phases of the GRA Universality marathon (Blueprint 16) are done:
- 8 Lean files, ~850 lines total
- 0 sorry, 0 native_decide, 0 external axioms, 0 Mathlib
- Typeclass + 5 instances + 5 isos + universality capstone + translations
- Blueprint success criteria met:
  ✓ GRAModel typeclass: 0 sorry, ∅-axiom
  ✓ 5 instances (NT, Graph, Analysis, Cohomology, HoTT, HigherAlgebra)
  ✓ 5 iso proofs (each Reading ≅ NT)
  ✓ Transitivity capstone
  ✓ ≥1 translation theorem (multiple, including novel prediction)

## Tier summary (cumulative)

| Tier | Programme | Status |
|------|-----------|--------|
| 1.1 | Per-layer ψ-kernel completeness | CLOSED |
| 1.2 | Arity c=2 Lean theorem | CLOSED |
| 1.3 | Pell-orbit Stern-Brocot extension | CLOSED (4/4) |
| 1.4 | α_em Step 5 purity | CLOSED |
| 2.1 | Hodge ↔ universe-chain | CLOSED |
| 2.2 | Cayley-Dickson ↔ Möbius | CLOSED |
| 2.3 | p-adic ↔ Möbius P mod-p | CLOSED |
| 3.2 | PRIMARY cup-image boundary framing | CLOSED |
| 4.1 | Catalog ↔ Lean parity | CLOSED |
| 5.2 | Universal P^n entry formula | CLOSED |
| 5.3 | Fibonacci Cassini from P^n det | CLOSED |
| 5.4 | Convergent det / Farey property | CLOSED |
| 5.5 | G139 self-form (iteration + uniqueness) | CLOSED |
| **16** | **GRA Universality (Phases 1–22)** | **★ CLOSED + PROMOTED + 401 PURE ★** |

## Genuinely open (next session targets)

  · **GRA carrier enrichment**: lift from Nat to Walk/Cochain/etc.
    (enrichment is beyond blueprint scope — optional Phase 7)
  · **Tier 3.1**: depth-3 cohomology (c = 3 extension)
  · **Tier 4.2**: Hadron baryon spectrum (channel-sum deployment)
  · **Tier 5.1**: propext unsealing (~20 DIRTY → PURE)
  · **G138 Pattern A**: Modulus-functor 4-way extension
  · **G138 Pattern F**: Multiplicity doctrine chapter
  · **CrossAddress → Functor**: triple-axis schema elevation
  · **New marathon candidate**: next blueprint from `blueprints/`

## Boot order

  · `seed/AXIOM/05_no_exterior.md` §5, §8.4
  · `theory/lens/unified_equivalence.md`
  · `theory/INDEX.md`
  · `lean/E213/ARCHITECTURE.md`
  · `theory/PROMOTION_CRITERIA.md`
