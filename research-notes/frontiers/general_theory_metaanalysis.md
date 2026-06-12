# General-theory meta-analysis — a long-term program

**Goal**: discover *genuine general theoretical structures* in the 213/DRLT
corpus by deep analysis + meta-analysis of recurring statement patterns across
Lean modules and theory documents — and separate them from coincidental
resonances / forcible maps using the adversarial debate method
(proponent / skeptic / formalist) that the slot-tower arc validated.

**Discipline (carried from the slot-tower marathon, `slot_tower_debate.md`)**:
a candidate "general structure" earns the label only if it is one of —
1. **shared mechanism**: one schema doing *generic work*, ≥2 genuine instances
   (e.g. `OrderWrap.no_order_of_wrap` — wrap kills every order witness);
2. **pinned distinction**: a binary/orthogonal *difference* with a real
   theorem on each side (e.g. bridge 1 finite/infinite certificate; bridge 4
   vector/sign).
— and is rejected if it is —
3. **vacuous container** (`{cert, iff}` / `LeveledReadout`: a tautology with no
   generic consumer), or
4. **resonance only** (a numeric/phenomenological coincidence with different
   objects/mechanisms — §5(b) level-2 ceiling vs `^`-wall).

Every Lean claim must be ∅-axiom (`tools/scan_axioms.py`).  Findings recorded
here; closed ones promoted to `theory/`.

## Synthesis — validated results so far (the deliverables)

Five genuine, adversarially-audited general-theoretical findings, all orbiting
**one object: the residue/Lens boundary** (`no-exterior` §5.1 on one side,
`object1_not_surjective` on the other):

1. **The α/β unification split + shared-generator criterion (C4).**  213
   unifies *abundantly* by parametric polymorphism (α: typeclasses — `Lens`,
   `ConjugationCodomain`, `iter`, `Ring213` — one proof, instances plug in) but
   *rarely* across independently-motivated phenomena (β).  **Genuine β-unification
   ⟺ a shared GENERATOR** (a common construction), not a shared slogan or number.
   Only `OrderWrap` (successor/orbit) and `HyperLadder` (`iter`) qualify; they sit
   at the count/successor floor.  Slogans (comm) and resonances (ceilings) fail
   for lack of a generator.

2. **The genuine-vs-forcible decision procedure (C4).**  generic-consumer test
   (does a theorem do work over the schema, or is it a tautological container?) +
   four-axis test (same objects/symmetry/predicate/mechanism, or coincidence?).
   It killed `LeveledReadout` and sorted every slot-tower bridge.

3. **The 2-axis readout classification + ℤ-uniqueness (C5).**  A readout has two
   independent axes: *faithfulness* (forgetful `count`/`Hyper` commute; faithful
   `vp`/`cut` don't) × *support-finiteness among faithful* (finite = discrete;
   infinite = continuum).  **ℤ/ℕ is the unique faithful-finite number system** —
   the only one with a finite equality certificate; every completion (real,
   `p`-adic, complex, signed) trades finiteness for infinite resolution.  Witnessed
   in Lean by `vp_eq_zero_of_gt` vs `cut_no_finite_certificate`.

4. **The failure-mode structure (C6).**  17/22 of CLAUDE.md's failure modes are
   *boundary errors* in two dual polarities (over-exteriorize / over-interiorize,
   forced by the two core axioms); 4/22 are orthogonal *discipline* failures
   (dialogue/hygiene/filing/clarity).

5. **The convergence (C4 ↔ C5 ↔ C6).**  A *forcible map* (C4 type-4) **is**
   *over-exteriorization* (C6 polarity 1); a *view-promoted-to-identity* (C6
   polarity 2) is what a *pinned distinction* (C4 type-2) refuses.  Unification,
   equality, and error are governed by **one two-sided boundary; the recurring
   failures are the two ways of falling off it.**

Method note: every one of these was *sharpened by an adversarial audit that
caught an over-claim* (C4's first "type-1 rare" draft; C6's "22/22"; C7's
"falsifies C4"; the deleted `LeveledReadout`).  The debate method is not
decoration — it is the load-bearing instrument, and it is itself an instance of
the decision procedure (β-candidates must survive the skeptic to count).

**Open / flagged**: C7 (physics closure form) — a sharpened *question* for the
originator, not a verdict (below).

## Candidate general structures under investigation

(Each gets: survey → debate → formalize-or-reject → record.)

- **C1. Equality = faithful readout agreement; discreteness = finite support.**
  Seed evidence (bridge 1, this branch): `cutEq` *defines* equality as per-level
  readout agreement; `vp_separation` is the *theorem* that the prime readout is
  faithful; `vp_eq_zero_of_gt` (finite support) vs `cut_no_finite_certificate`
  (unbounded) pin the discrete/continuum axis.  General question: do *all* 213
  equality notions factor through one readout-faithfulness shape, and is
  "discrete ⟺ faithful readout has finite support" a general theorem?

- **C2. Commutativity = order-forgetting = atom-indistinguishability =
  simultaneity.**  The repo asserts this as "one handle" (CLAUDE.md;
  `slot_tower_crossdomain.md` §5).  General question: is there a single Lean
  structure of which `add_comm_from_append`, `mul_comm_from_grid`,
  `conv_comm`, `append_comm` are instances — commutativity ⟺ a transpose/swap
  symmetry of the generating operation?

- **C3. The "regularity ceiling" typology.**  Where regularity runs out
  (`^`-wall, ORIGIN_RAW level-2, `mod p` wrap, no-finite-certificate).  §5(b)
  ruled level-2 vs `^`-wall a *resonance*.  General question: is there a
  genuine meta-structure to "ceilings", or are they all distinct?  (Default:
  skeptical — likely resonance, per the §5(b) precedent.)

- **C4. The meta-theory of genuine-vs-forcible itself** (the decision
  procedure above).  Synthesised from this session's validated/rejected cases.

## C6 — the structure of the failure-modes catalog (validated 17 + 4)

Tested whether CLAUDE.md's ~22 failure modes reduce to one **boundary-error**
with two dual polarities.  Adversarially audited (the audit itself risked the
"external classification" failure mode); verdict **GENUINE, honestly bounded**:

- **17 / 22 are boundary errors** — mis-locating the residue/Lens boundary, in
  two dual polarities forced by the two core axioms:
  - **(1) over-exteriorize** — import a frame / ruler / object / classification
    from outside (violates **no-exterior**, `05_no_exterior.md` §5.1).  Rows:
    importing dichotomy, stereotype matching, external classification,
    metaphysical framing, deferred-ontology dichotomy, fine-tuning-as-forbidden,
    external-ruler smuggling, ℤ/sign-as-exterior, 0/∞ mixed-status,
    DRLT-validation-as-goal, transcendental-as-exterior, `^`-wall-via-imported.
  - **(2) over-interiorize** — promote a Lens-*reading* to the residue itself
    (violates `object1_not_surjective`: the residue is outside *every* view's
    image).  Rows: substrate metaphor, count-Lens-as-Raw, universe-constant,
    equivalence-pluralism, view-promoted-to-identity, quotient-as-ontology.
- **4 / 22 are orthogonal *discipline* failures** (not boundary errors):
  self-soothing agreement (dialogue), legacy-deletion narration (narrative
  hygiene), tier mismatch (filing), fog jargon (clarity).

The reduction is **not** itself "external classification": the two polarities
are the literal content of the two core axioms, not an imposed scheme — and the
4 exceptions are *named as orthogonal*, not stretched to fit.  (The first-pass
"22/22" was the usual over-claim; corrected to 17+4.)

### Convergence — C4 and C6 are the same boundary, at two scales

The two independent meta-axes meet: a **forcible map** (C4's type-4 vacuous
unification — `LeveledReadout`) *is* polarity-(1) **over-exteriorization** at
the meta level — importing a unifying schema the structure does not grant.  And
a **view-promoted-to-identity** (C6 polarity 2) is what a *pinned distinction*
(C4 type-2) refuses to do — it keeps each reading a facet, never the thing.  So
the unification typology (C4), the readout classification (C5), and the
failure-mode structure (C6) all orbit **one object: the residue/Lens
boundary** — no-exterior on one side, `object1_not_surjective` on the other.
Genuine 213 work is staying on that boundary: import nothing from outside
(C4-α only, never a forcible map), and promote no reading to the thing (keep
distinctions — C4 type-2, C5's grid, C6 polarity-2 avoided).

This convergence is the program's deepest finding: **the discipline of 213 —
unification, equality, and error alike — is governed by a single two-sided
boundary, and the recurring failures are the two ways of falling off it.**

## C8 — convergence tested in the cohomology/cardinality-cutoff domain → CORROBORATES + EXTENDS

Probed a major unexamined domain (the cardinality-cutoff principle +
`Cohomology/Fractal`) to test whether the residue/Lens boundary organises the
*whole* corpus or only where the program had looked.  Verdict: **corroborates,
and adds one genuinely new structural element.**

- **Orthogonal to the unification typology (C4), not captured *or* refuted by
  it.**  The cutoff makes **no** unification claim — it is a *scale-matching*
  methodology: an external sequence `f` (Aurifeuillean) and an internal
  complexity class `H_k` (Hunter depth ≤ k) are *deliberately different*
  construction trees, and the content is precisely that they **coincide at
  small `k`, then separate forever**.  No shared generator is claimed (so not
  type-1); the coincidences (`29 = L_1 = P_5 = Lucas L_7`) are type-3
  resonances; the asymptotic separation is a type-2 distinction *refined*.
- **Sits exactly on the boundary.**  `H_k`, `M_k = max H_k` are **Lens-
  parametric readouts** (a truncation = a resolution = a view;
  `ConfigCount.lean`: "numerical readouts are Lens outputs, parametric in base
  and level").  The **deleted `5²⁵ = N_U`** claim is textbook
  *over-interiorization* (C6 polarity 2 / "universe-constant framing"):
  promoting the count-Lens readout `configCount 2 = 5²⁵` to a residue constant
  `N_U`.  The principle's own structure *catches* this.

**The extension — a second boundary-respecting instrument.**  Beyond the
unification decision-procedure (for cross-domain *schema* candidates), the
cutoff exhibits the **literal→refined diagnosis** for *Lens-parametric*
candidates (a universal claim over a truncation/level):

  1. **locate** — a Lens-slice (fixed small `k`) where external and internal
     measures coincide;
  2. **diagnose** — prove the *literal* `∀k ∀m` form **false** (no fixed
     Lens-level `k` captures the asymptotics — this *is* `object1_not_surjective`:
     no single view surjects onto the whole);
  3. **refine** — requantify with the level **first** (`∀k ∃m₀ ∀m≥m₀`),
     acknowledging the truncation index is a *parametric axis*, never a fixed
     residue property.

This is the methodological **dual** of the unification procedure: the procedure
catches *over-exteriorization* (a forcible cross-domain schema); the
literal→refined diagnosis catches *over-interiorization* (a Lens-parametric
readout frozen into a constant / a naive universal).  Both are tools for
staying on the one boundary — so the boundary framework now has a matched pair
of instruments, one per polarity.  **The convergence finding survives a
genuinely independent domain and gains a second tool — strong evidence it
organises the corpus, not just the slot-tower region.**

## C7 — does C4 hold in the physics branch? (a sharpened question, NOT a verdict)

Tested the shared-generator criterion on the DRLT **closure form**
`O = R(NS,NT,d,c) · Π(1 + κ_i·α_i^{n_i})` (`rust-engine/docs/closure-algorithm.md`).
The surveyor returned a strong "fitted template" verdict; **two corrections are
required before recording anything**, because this touches the originator's
core physics and the verdict's *logic* was inverted:

1. **Logic correction.**  Even *if* the closure form were a per-observable fit
   rather than a genuine generator, that would **corroborate** C4 (apparent
   high-level unifications are usually forcible / not genuine shared
   generators — exactly C4's thesis), **not falsify** it.  C4 is a claim about
   the *rarity* of genuine generators at height; a forcible physics template is
   an *instance* of that rarity, not a counterexample.  (The surveyor's
   "falsifies C4" verdict is rejected on this ground.)

2. **Contested premise — left open for the originator.**  Whether the form is
   0-parameter (CLAUDE.md: "0 free parameters = structural absence") or a
   structurally-constrained *fit* hinges on **one precise question**: is the
   atomic-integer search space (κ ∈ combinations of `NS,NT,d,c`, bounded) tight
   enough that a per-`O` match is *forced*, or loose enough that *some* match is
   generically findable (numerology)?  This is the originator's physics; it is
   not mine to adjudicate.  Genuine data the survey did surface (worth keeping):
   - the κ_i/n_i are **discovered by exhaustive search** (`atomic_hunter.rs`)
     over a structurally-bounded set, not derived top-down — documented openly;
   - the repo **self-flags `g_n`** (needs coefficient `19`, prime, *not*
     decomposable into `NS,NT,d,c`) as a candidate **falsifier** — honest
     engagement, not hiding (cf. the *deleted* `5²⁵=N_U` claim: the repo already
     self-corrects numerology);
   - observables nearest the **counting floor** (`N_gen=3=NS²−1`, `1/α_3=8`,
     `m_p/m_e≈6·π⁵`) are bare / 0-correction; the precision constants take 2–3
     nested α-corrections.  This is the *opposite* slope to the math branch
     (where the floor unifies and height diverges) — in physics the floor is
     bare and **height needs more correction terms** — which is itself a
     genuine, interesting cross-branch contrast worth understanding, **not**
     evidence either way on the fit question.

**Status: OPEN, flagged to the originator.**  The right framing is a question —
*"is the atomic search space structurally forced (0-parameter) or generically
matchable (numerology), and what distinguishes the genuine-generator observables
(`N_gen`, `1/α_3`) from the correction-heavy ones (`g_p`, `1/α_em`)?"* — not a
verdict that the physics is overfitted.  Pursuing it needs the originator's
steer (it is their core deployment, and the failure mode "DRLT-validation-as-
the-goal" lurks if a math-side critic grades it by an external bar).

## Log

- (init) Program opened; surveyor team dispatched on C1–C3; C4 synthesised
  from the slot-tower marathon record.
- C2 (different mechanisms, one principle) + C3 (resonance only) returned;
  C4/C5 drafted.
- **C4 adversarially audited and CORRECTED**: the first "type-1 is rare" draft
  had selection bias (ignored the polymorphic typeclass infrastructure — Lens
  22+, ConjugationCodomain 7+, iter, Ring213 59+, all genuine type-1).  Sharper
  result: the α/β split — *parametric* unification abundant (free, by
  construction), *cross-domain conceptual* unification rare (the residue
  withholds it).  This is now the program's central finding.
- C1 (equality/readout inventory) still running — needed to finish the C5
  2-axis readout grid (faithfulness × support-finiteness) across all number
  systems.
- **C6 (failure-mode structure) audited and validated**: 17/22 are boundary
  errors (two dual polarities forced by no-exterior + object1_not_surjective);
  4/22 are orthogonal discipline failures.  **C4 ↔ C6 convergence** found: a
  forcible map IS over-exteriorization; the whole discipline orbits the one
  residue/Lens boundary.  This is the program's deepest finding.
- C5 grid completed by direct survey (ℤ unique faithful-finite); strengthened
  with `zpseq_no_finite_certificate` (p-adic continuum witness) + the free-vs-
  constrained completion sub-axis (a "shared generator" bonus claim was made
  and then *retracted reflexively* — the discipline working on the author).
- **C8 (cohomology/cardinality-cutoff) → CORROBORATES + EXTENDS**: the boundary
  framework organises a genuinely independent domain, and gains a *second*
  instrument — the literal→refined diagnosis (dual to the unification
  decision-procedure; catches over-interiorization of a Lens-parametric readout).
- **C7 (physics cross-branch) — OPEN, flagged to originator.**  Surveyor's
  "closure form is a fit / falsifies C4" verdict was *logic-corrected* (a
  forcible template would *corroborate* C4, not falsify it) and reduced to a
  precise open question about the structural-forcing of the atomic search space.
  Touches core physics — needs the originator's steer; not adjudicated here.

## Survey results

### C2 — commutativity / atom-indistinguishability → DIFFERENT MECHANISMS, one PRINCIPLE

Surveyed every `*_comm` proof and its *mechanism* (not statement):

| op | theorem | proof mechanism | what the readout erases |
|---|---|---|---|
| append | `UnitList.append_comm` | bare list induction (base fact) | — (the floor) |
| `+` | `UnitList.add_comm_from_append` | `count (l₁++l₂) = count (l₂++l₁)` via `append_comm` | **order** |
| `×` | `UnitGrid.mul_comm_from_grid` | grid transpose preserves cell total (`heads_tails_total`) | **layout** |
| `conv` | `Convolution213.conv_comm` | split-endpoint reversal of `natSplits` | **cut-endpoint order** |
| `^` | `HyperAssoc.pow_not_comm` | `decide` witness `2^3≠3^2` | **nothing** (base/exp distinguishable) |

**Verdict**: the asserted "one handle" (comm ⟺ atom-indistinguishability ⟺
simultaneity) is **not** a shared Lean schema — the three comm proofs cite
genuinely different crux lemmas (`append_comm` / `heads_tails_total` /
`conv_peelL/R`); indistinguishability is *embedded in each structure*, never
*invoked as a hypothesis*.  A `comm_iff_atoms_indistinguishable` schema does
not factor.  **But** a genuine general *principle* is real: **commutativity =
invariance of the defining readout under the generating structure's reordering**
— "what the structure forgets is what commutes."  `+`/`×`/`conv` each commute
because their readout (`count`/`total`/the cut) is invariant under a
structure-specific swap; `^` commutes nothing because its readout forgets
nothing.  This is **type-(2)** (a shared principle whose instances do not share
a proof), not type-(1) shared mechanism.  [Refined candidate C2′ below.]

### C3 — regularity ceilings → RESONANCE ONLY (no general ceiling theory)

Enumerated 9 boundary phenomena (`^`-wall comm/assoc; `^`-wall fold/transcendence;
ORIGIN_RAW level-2 past-completeness; `mod p` wrap; cut no-finite-certificate;
vp finite support; PairOp bi-distributivity impossibility; Raw determinism
step1→3; async MemEq depth).  Applied the §5(b) four-axis test (same objects?
same symmetry/predicate? same mechanism? or numeric coincidence?) to every
candidate pair.

**Verdict**: every cross-phenomenon unification is **rejected** except the two
already-closed genuine ones (`OrderWrap.no_order_of_wrap` schema; `HyperLadder`
recursion) and the one pinned distinction (finite/infinite certificate).  The
"regularity runs out at a rung" shape is *phenomenological*, not a mechanism;
the breakdowns have independent causal stories (type-promotion vs syntactic
subterm-closure vs orbit-wrap vs support-finiteness).  A general "ceiling
theory" would require provably-false bridging lemmas — stereotype-matching.
No deliverable, by design.

## Meta-theorem (C4) — the architecture of 213 unification

**First draft of C4 over-claimed** ("type-1 unification is rare, essentially
only OrderWrap + HyperLadder") and was **corrected by an adversarial audit**
that found abundant type-1 unification the slot-tower survey had missed:
`Lens` (22+ instances, shared polymorphic proofs `equiv_refl/symm/trans`,
`refines_*`), `SelfRecognising.ConjugationCodomain` (7+ instances `ZI/Z2/ZOmega/
ZSqrt D`, generic `specLens_swapMatching`), `Iterate213.iter` (polymorphic
`iter_add/iter_mul`), `Ring213` (59+ instances).  The first draft had
**selection bias**: it surveyed the cross-domain *narrative bridges* and
generalised to the whole corpus.

The corrected — and sharper — claim distinguishes **two kinds of unification**:

> **(α) Parametric (infrastructure) unification is ABUNDANT and free.**  One
> proof generic over a structure; instances plug in *by construction* (every
> new `Lens`, `ConjugationCodomain`, `Ring213` instance, every `iter` over a
> type).  This is 213's standard tool for shared infrastructure.
>
> **(β) Cross-domain *conceptual* unification — two *independently motivated*
> phenomena turning out to share one mechanism — is RARE.**  Across the
> slot-tower marathon (bridges 1–4, §5 a/b), commutativity, and ceilings, only
> `OrderWrap` (ℤ-order ⟷ mod-p wrap) and `HyperLadder` (the tower as one
> `iter`-recursion) genuinely unified.  The rest are type-2 *pinned
> distinction*, type-3 *resonance*, or type-4 *vacuous/forcible*.

The sharp content: **213's abundant parametric polymorphism does not extend to
its cross-domain phenomena.**  You cannot typeclass your way from `cutEq` to
`vp`-equality, or from append-commutativity to grid-commutativity — these have
*different proofs* despite the unifying slogan (C2).  Parametric unification
works *within* a chosen structure; conceptual unification *across*
independently-arising structures is what the residue mostly withholds —
the `no-exterior` / `object1_not_surjective` theme at the meta level (no single
*view* unifies the domains; each must be re-derived, not mapped).  This is why
a naive "find the shared schema" search keeps producing forcible maps
(`LeveledReadout`) that the structure rejects.

### C4 refinement — the *shared-generator* criterion (why α works and β rarely does)

Interrogating the α/β asymmetry: `OrderWrap` and `HyperLadder`, the two genuine
β-successes, are *themselves* parametric (α) schemas — a successor-structure
`(M,s,a)` with an orbit; the `iter` recursion.  So a genuine conceptual (β)
unification is precisely **the discovery that two independently-motivated
phenomena are instances of one shared GENERATOR (a common construction)** —
upon which β *collapses into* α.  The criterion, sharp and testable:

> **Genuine cross-domain unification ⟺ a shared *generator* (a common
> construction both phenomena are built from), not a shared *slogan* or a shared
> *number*.**

Checked against the corpus:

| candidate | shared generator? | outcome |
|---|---|---|
| ℤ-order ⟷ mod-p wrap | YES — successor map + orbit (`OrderWrap`) | β-success (→α) |
| `+`,`×`,`^` tower | YES — `iter` against the count (`HyperLadder`) | β-success (→α) |
| `+`-comm ⟷ `×`-comm | NO — list-append vs grid-transpose (C2) | slogan only (different proofs) |
| cut-equality ⟷ vp-equality | NO — cut-readout vs prime-readout (C1) | pinned distinction (finite/∞) |
| shape ⟷ curvature | NO — factorization vs degree-difference (bridge 4) | pinned distinction (vector/sign) |
| level-2 ceiling ⟷ `^`-wall | NO — tree-depth vs operation-arity (§5b) | resonance (numeric coincidence) |

The pattern: the genuine β-successes share a **combinatorial generator at the
count/successor primitive** (ℕ-iteration); the failures sit higher (reals,
primes, curvature, syntax) where the generators are genuinely domain-specific.
So **unification distance grows with structural height**: the residue's
domains share generators near the counting floor and diverge above it — they
are re-derived, not mapped (`object1_not_surjective`).  The "generic-consumer
test" of the decision procedure *is* the shared-generator test: a real
generator yields theorems doing work over instances; a fake schema
(`LeveledReadout`) has no generator, only a relabeling.

The **decision procedure** that sorts a *conceptual* (β) candidate is the
reusable tool (parametric (α) unification needs no sorting — it is shared by
construction):

1. propose a single schema;
2. **generic-consumer test** — does a theorem do *generic work* over the
   schema (rule something out / derive something), or is it a tautological
   `{data, iff}` container? (kills type-4: LeveledReadout, naive comm-schema);
3. **four-axis test** — same objects / symmetry / predicate / mechanism, or
   numeric coincidence? (sorts type-1 vs type-3);
4. if neither a shared proof nor a coincidence, look for a **theorem on each
   side pinning a genuine binary/orthogonal difference** (type-2).

C4 is a `theory/` meta-chapter, not a Lean theorem (it is *about* the corpus).
C1 (equality/readout) pending — the strongest *formalizable* candidate.

### C2′ — comm = readout-erasure: non-vacuity check → SCHEMA VACUOUS, PRINCIPLE GENUINE

Applying step 2 (generic-consumer test): the schema
`op a b = R (gen a b)` + `R (gen a b) = R (gen b a)` ⟹ `op a b = op b a`
is a **tautology** — `op`-commutativity literally *is* the readout-swap-
invariance, so the "schema" restates its own hypothesis (the same defect
that killed `LeveledReadout`).  The genuine content is entirely in proving
the swap-invariance per structure (`append_comm` / transpose / split-reverse).
So C2′ is **not** a type-(1) schema.  Verdict: principle genuine, schema
rejected — consistent with the decision procedure.

### C5 (emergent, the strongest cross-cutting candidate) — faithfulness ⟂ commutativity

C1 and C2 *cross*.  Read an operation as `op a b = R (gen a b)` (a readout `R`
of a generating structure `gen`).  Then:

- **forgetful `R` (large fibers) ⇒ commutativity.**  `+` = `count` of a list
  (forgets order, `add_comm_from_append`); `×` = `total` of a grid (forgets
  layout, `mul_comm_from_grid`).  What `R` erases is precisely the swap.
- **faithful `R` (trivial fibers) ⇒ NON-commutativity.**  At `^` the readout
  keeps base/exponent in *different slots* (the `iter` count vs the iterated
  `f`), so the swap is visible — `pow_not_comm`.  The prime readout `vp` is
  *faithful* (`vp_separation`, UFD) — and it is exactly the `×`→`^` rung where
  the exponent vector "remembers which prime" (`vp_mul`) that commutativity
  dies.

So **commutativity and readout-faithfulness are dual**: the *same* property
(how much the readout forgets) that makes the equality-certificate small/large
(C1: finite support = discrete = faithful-and-finite) governs whether the
operation commutes.  The tower is the ladder of *decreasing forgetting*:
`append` (keeps order) → `+`/`×` (forget order/layout, commute) → `^` (keeps
the slot split, faithful, non-comm).  This ties C1 (faithfulness / certificate
size), C2 (commutativity), and the `HyperLadder` tower into one axis:
**how much the readout forgets**.

**Refinement — TWO independent axes of a readout (not one).**  Testing the
duality on the `HyperLadder` showed it is sharper than "one forgetting axis":

- **Axis A — faithfulness ⇒ (non)commutativity.**  Forgetful readout (huge
  fibers: `count`, `total`) ⇒ commutes; faithful readout (trivial fibers: the
  base/exp slot split) ⇒ non-comm.  On the ladder this is a *bounded window*:
  `hyperop k` commutes exactly for `k ∈ {1,2}` (`+`,`×`); `k=0` (successor
  *ignores* the base) and `k=3` (`^` *distinguishes* base/exp) both fail — for
  *different* reasons (ignore an argument vs. split roles).  So even the window
  has no type-(1) proof (k=1, k=2 commute by different mechanisms, C2) — a
  single `hyperop_comm_iff` would be a vacuous bundle (§5(a) lesson).  Recorded
  as observation, not forced into one theorem.
- **Axis B — among *faithful* readouts, support-finiteness ⇒ discrete/continuum.**
  `vp` faithful **and** finite-support (cofinitely trivial, `vp_eq_zero_of_gt`)
  = discrete; `cut` faithful **and** infinite-support
  (`cut_no_finite_certificate`) = continuum.

`count` is *forgetful* (off axis B entirely — it commutes, and its certificate
question is moot).  `vp` is *faithful + finite* (discrete; and it is exactly
`vp`'s distinguishing that makes `^` non-comm).  `cut` is *faithful + infinite*
(continuum).  So readouts classify on a genuine **2-axis grid**
(faithfulness × support-finiteness), and the corpus's number systems / tower
rungs sit at distinct cells.  This is a real general *classification* (type-2
structure), not a single forced theorem — its honesty is the point (C4).

**The grid, completed** (equality definitions surveyed directly):

| readout / equality | faithful? | support | cell |
|---|---|---|---|
| `count` (ℕ via `UnitList`) | **no** (forgets order) | — | forgetful → `+` commutes |
| `Hyper.cofiniteEquiv` (`∃N ∀n≥N`) | **no** (forgets finite prefix) | — | forgetful (cofinite quotient) |
| `vp` (ℤ/ℕ prime-exponent) | yes (UFD, `vp_separation`) | **FINITE** (`vp_eq_zero_of_gt`) | faithful + finite = **discrete** |
| `cutEq` (reals) | yes (definitional) | infinite (**`cut_no_finite_certificate`**) | faithful + ∞ = continuum |
| `ZpSeqEquiv` (`p`-adics, `∀k digits`) | yes (definitional) | infinite (**`zpseq_no_finite_certificate`**) | faithful + ∞ = continuum |
| `Complex` (cut pair) | yes | infinite (per component) | faithful + ∞ = continuum |
| `SignedCut` (cut + sign) | yes | infinite | faithful + ∞ = continuum |

Two genuinely independent axes confirmed, and a **clean novel corollary**:

> **ℤ/ℕ (the `vp` readout) is the *unique* faithful-finite number system — the
> only one with a finite equality certificate.  Every completion (real,
> `p`-adic, complex, signed/quaternion/octonion) is faithful-at-every-level but
> *infinite*: it trades finiteness for unbounded resolution.  The forgetful
> readouts (`count`, `Hyper`'s cofinite quotient) lie off the discrete/continuum
> axis entirely — they *identify* (large fibers), which is why `count` yields
> commutativity and `Hyper` is a quotient.**

So the discrete/continuum boundary is precisely **"reconstructible from
*finitely* many readouts"**, and it cuts the number tower at exactly one place:
between ℤ/ℕ and its completions.  The cut is now witnessed in Lean on **three**
sides — `vp_eq_zero_of_gt` (ℤ, finite) vs two *independent* continuum witnesses,
`cut_no_finite_certificate` (reals) and `zpseq_no_finite_certificate`
(`p`-adics, added this session) — so axis B is confirmed real across genuinely
different completions (an archimedean and a non-archimedean one), not an
artifact of the reals.

(*Decision procedure applied reflexively — a tempting "shared generator" claim
here does **not** survive, and the reason is itself a finding.*  The two
witnesses are **not** the same construction: the `p`-adic one is a **single-digit
flip** (valid because *any* digit sequence `ℕ → Fin p` is a genuine `p`-adic — a
**free** function-space), while the real one needs two **close rationals**
(`N/(N+1)`, `(N+1)/(N+2)`) — a single-flip Bool function is not monotone, so not
a valid Dedekind cut; reals are a **monotone-constrained** function-space.  So
only the no-finite-certificate *statement* is shared (type-(3)/(2)); the
witnesses differ in kind.  The genuine content is the **free vs constrained
completion** distinction: `ℚ_p` is the unconstrained product `∏ Fin p`, `ℝ` the
monotone sub-object of `2^(ℚ)` — both infinite-certificate, but for different
structural reasons.  The decision procedure catching the author mid-celebration
is the discipline working as designed.)
