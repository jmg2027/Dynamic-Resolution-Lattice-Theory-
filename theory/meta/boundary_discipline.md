# Boundary discipline — the one object behind unification, equality, and error

A meta-analysis chapter.  Where the other `theory/meta/` chapters narrate the
scanner suite and the cutoff methodology, this one states a single structural
finding that organises the repository's *practice*: **213's unification,
equality, and error are all governed by one two-sided object — the residue/Lens
boundary** (`no-exterior`, `seed/AXIOM/05_no_exterior.md` §5.1, on one side;
`object1_not_surjective` / `FlatOntologyClosure`, the residue outside every
view's image, on the other).  The recurring failures are the two ways of
falling off that boundary, and there is a matched pair of instruments — one per
side — for staying on it.

Working log + open threads: `research-notes/frontiers/general_theory_metaanalysis.md`.
Method: each claim below was sharpened by an adversarial audit that caught an
over-claim (several retractions, one reflexive) — the debate discipline of
`research-notes/frontiers/slot_tower_debate.md`, applied to the corpus itself.

## 1. Two kinds of unification (α and β), and the shared-generator criterion

213 unifies in two very different ways, and conflating them is the root of
most forced "discoveries".

- **α — parametric unification — abundant and free.**  One proof generic over
  a structure; instances plug in *by construction*.  This is the repo's
  standard infrastructure: `Lens` (22+ instances, shared `equiv_refl/symm/trans`,
  `refines_*`), `SelfRecognising.ConjugationCodomain` (`ZI/Z2/ZOmega/ZSqrt D`,
  generic `specLens_swapMatching`), `Iterate213.iter` (`iter_add/iter_mul`,
  polymorphic), `Ring213` (59+ instances).
- **β — cross-domain conceptual unification — rare.**  Two *independently
  motivated* phenomena turning out to share one mechanism.  Across the
  slot-tower marathon, commutativity, and the regularity ceilings, only
  **`OrderWrap`** (ℤ-order ⟷ mod-`p` wrap, via a successor structure + orbit)
  and **`HyperLadder`** (`+,×,^` as one `iter`-recursion) genuinely unify.

The criterion that separates a genuine β-discovery from a forcible map:

> **Genuine cross-domain unification ⟺ a shared *generator* — a common
> construction both phenomena are built from — not a shared *slogan* or a
> shared *number*.**

A genuine β-discovery *is* the recognition that two phenomena are instances of
one parametric (α) schema, upon which β collapses into α (`OrderWrap` and
`HyperLadder` are themselves parametric schemas).  The genuine β-successes share
a **combinatorial generator at the count/successor floor** (ℕ-iteration) — and,
sharpened, it is *literally one generator*: `OrbitIsIter.orbit_eq_iter` proves
`OrderWrap`'s orbit **is** `Iterate213.iter` (the count iterating the
successor), and `HyperLadder.hyperop_succ` is `iter` iterating the rung below.
So the two β-successes are two deployments of **the** count-floor generator,
`iter`, whose second argument *is* the count-Lens `ℕ` — falsifiable form: *any
future β-success will be `iter`-derived*.  The
failures sit higher — `+`-comm vs `×`-comm (append vs grid, no shared proof),
cut-equality vs `vp`-equality (different readouts), shape vs curvature
(factorization vs degree-difference).  **Unification distance grows with
structural height**: the residue's domains share generators near the counting
floor and diverge above it — they are *re-derived, not mapped*
(`object1_not_surjective`).

## 2. The failure modes are two boundary errors plus a remainder

Of `CLAUDE.md`'s ~22 named failure modes, **17 are boundary errors** in two
dual polarities, *forced by the two core axioms* (not an imposed classification):

- **(1) over-exteriorize** — import a frame / ruler / object / classification
  from outside (violates **no-exterior**).  E.g. stereotype matching, external
  classification, external-ruler smuggling, ℤ/sign-as-exterior,
  transcendental-as-exterior, DRLT-validation-as-goal.
- **(2) over-interiorize** — promote a Lens-*reading* to the residue itself
  (violates **`object1_not_surjective`**).  E.g. count-Lens-as-Raw,
  universe-constant framing, equivalence-pluralism, view-promoted-to-identity,
  quotient-as-ontology.

The remaining **4 are orthogonal *discipline* failures** — not boundary errors:
self-soothing agreement (dialogue), legacy-deletion narration (narrative
hygiene), tier mismatch (filing), fog jargon (clarity).

## 3. The convergence — one boundary behind §1 and §2

The two analyses meet exactly:

- a **forcible map** (a vacuous unifier — the deleted `LeveledReadout`) **is**
  polarity-(1) **over-exteriorization** — importing a unifying schema the
  structure does not grant;
- a **view-promoted-to-identity** (polarity 2) is what a genuine **pinned
  distinction** *refuses* — it keeps each reading a facet, never the thing.

So unification (§1), equality, and error (§2) are governed by **one two-sided
boundary**.  Genuine 213 work is *staying on it*: import nothing from outside
(α only, never a forcible β), and promote no reading to the thing (keep the
distinctions).

## 4. The matched pair of instruments

Each side of the boundary has its own boundary-respecting tool — and they are
duals.

- **For cross-domain *schema* candidates (the over-exteriorize side): the
  unification decision-procedure.**
  1. **generic-consumer test** — does a theorem do *generic work* over the
     proposed schema (rule something out / derive something), or is it a
     tautological `{data, iff}` container?  (This is the shared-generator test:
     a real generator yields theorems that work over instances; a fake one only
     relabels.  It killed `LeveledReadout`.)
  2. **four-axis test** — same objects / symmetry / predicate / mechanism, or a
     numeric coincidence?  (Sorts genuine unification from resonance — §5(b)
     level-2 ceiling vs `^`-wall.)
  3. If neither a shared proof nor a coincidence, look for a **theorem on each
     side pinning a genuine binary/orthogonal difference** (a pinned
     distinction — bridge 1's finite/∞ certificate, bridge 4's vector/sign).

- **For Lens-*parametric* candidates (the over-interiorize side): the
  literal→refined diagnosis** (the cardinality-cutoff methodology,
  `theory/meta/cardinality_cutoff_principle.md`).
  1. **locate** — a Lens-slice (a fixed level / truncation `k`) where two
     measures coincide;
  2. **diagnose** — prove the *literal* universal (`∀k ∀m …`) **false**: no
     fixed Lens-level captures the whole (`object1_not_surjective` again);
  3. **refine** — requantify with the level *first* (`∀k ∃m₀ ∀m≥m₀ …`),
     acknowledging the truncation index is a *parametric axis*, never a fixed
     residue property.  (The deleted `5²⁵ = N_U` claim is the canonical error
     this catches — a count-Lens readout frozen into a universe constant.)

The decision-procedure catches **over-exteriorization** (a forcible schema);
the literal→refined diagnosis catches **over-interiorization** (a parametric
readout frozen into a constant).  One instrument per polarity.

## 5. The framework is complete (two sides) — and `object1_not_surjective` reads at three scales

A natural worry: is there a *third* axis the two-sided boundary misses — a
**temporal / process / convergence** structure?  The corpus says, recurrently,
that *process is a property of the pointing (the approximant run), never of the
residue* (presentation-invariant, "reached by none, only converged to").  Tested
directly: this is **not** a third axis — it is the **temporal face of
`object1_not_surjective`**.  Instantiate the views as *pointings* (runs,
schedules, truncation levels) and the non-image as the *residue* (the limit, the
real, the invariant value): non-surjectivity says no finite stage reaches the
residue, so all process is approach-from-a-view — exactly the recurring shape.

So the over-interiorize axiom reads at **three scales**, unifying independently
discovered phenomena as one face:

- **logic scale** — `FlatOntologyClosure.object1_not_surjective`: `Raw ↛`
  predicates; the residue is the non-image of the self-cover.
- **process scale** — the residue is invariant under the run:
  `Real213.PresentationDependence.rcut_rescale` (the real is rescaling-invariant;
  modulus / holonomicity / certificate-depth are of the *pointing*),
  `Real213.ModulusComposition.reschedule_limit_eq` (rescheduling does not move
  the limit), `Theory.Raw.Async.level3_diverges` (the run is underdetermined past
  the first composite; the order is invariant), `HyperLadder` (the count is the
  clock — a view, not the tower).
- **descriptive scale** — no finite catalog covers its own diagonal:
  `Padic.NuEscape.mul_carry_nu_residue` (`add_carry_le_one` finite vs
  `mulCarry_unbounded` — the *same* value `(-1)²=1` carries a bounded and an
  unbounded process, so finite-state is a property of the *pointing*, not the
  number); `theory/essays/methodology/why_the_reframing_recurs.md`.

This is genuine *deepening* (the unification of presentation-dependence, async
determinism, finite-state, and the weld under one face was a discovery), but it
adds **no new primitive** — confirming the boundary has exactly two sides.

## 6. Corroboration, and a Lean-backed corollary

The boundary framework has been tested in six independent regions of the
corpus and corroborated in every math/meta one (the slot-tower bridges,
commutativity, the regularity ceilings, the readout/number-system inventory,
the failure-mode catalog, and the cohomology/cardinality-cutoff machinery).
One physics-branch question (the DRLT closure form — is its atomic search space
structurally forced, or generically matchable?) is held open for the originator
(`general_theory_metaanalysis.md` C7); whichever way it resolves it *corroborates*
the framework (a forcible template is an instance of the rarity of genuine
high-level unification, not a counterexample).

A concrete, ∅-axiom corollary anchors the equality side (the readout
classification, `general_theory_metaanalysis.md` C5).  A number system's
equality is *readout-agreement*; the readout has two independent axes —
*faithfulness* and, among faithful readouts, *support-finiteness* — and:

> **ℤ/ℕ is the unique faithful-finite number system: the only one whose
> equality has a *finite* certificate.**  Every completion trades finiteness
> for faithful-at-every-level (infinite resolution).

Witnessed on three sides in Lean: `FoldCriterion.vp_eq_zero_of_gt` (ℤ —
`vp p n = 0` for `p > n`, support ⊆ `[2,n]`, finite) against two *independent*
continuum witnesses, `Real213.Core.CutNoFiniteCert.cut_no_finite_certificate`
(reals, archimedean) and `Padic.NoFiniteCert.zpseq_no_finite_certificate`
(`p`-adics, non-archimedean).  The discrete/continuum boundary is precisely
"reconstructible from *finitely* many readouts", and it cuts the number tower
at exactly one place — between ℤ/ℕ and its completions.  (The two continuum
witnesses do *not* share a generator — `p`-adics are a free function-space
`∏ Fin p`, reals a monotone-constrained sub-object of `2^ℚ` — a distinction the
decision-procedure surfaced when a "shared generator" claim was tested and
retracted.)

---

The single sentence: **213 has one boundary, two sides, two failure-polarities,
and two instruments; doing 213 well is the discipline of staying on it —
importing nothing from outside, and mistaking no view for the thing.**
