# Session handoff

Branch: `claude/tower-research-analysis-3uWqd`

## This session — tower analysis → Raw branching → the residue → self-covering

Started as a "tower" research audit; became a foundational thread on what the
residue (the "1" in 2-1-3) is.  All commits ∅-axiom where Lean; pushed.

### Constructive deliverables (all PURE)

  - **`Theory/Raw/PrimitiveTower.lean`** (8 PURE) — the most primitive tower:
    `rawTower n = a/(a/(…/b))`, the single `slash` (self-pointing) arrow
    iterated; `depth = level`, `depth < leaves` every rung.
  - **`Lens/FlatOntologyClosure.lean`** (6 PURE) — the self-covering closure
    *limit* half: `object1_injective` (Raw self-covers as predicates,
    faithful) ∧ `object1_not_surjective` (Cantor: the predicate space is not
    in the image = the residue surplus).  `residue_witnessed` names a concrete
    inhabitant of the gap: `undifferentiated := fun _ => true` (the `Raw→Bool`
    shadow of `constLens`) — no Raw's indicator equals it.  Complements the
    pre-existing *positive* half `Lens/PredicateSelfEncoding.lean` (7 PURE,
    definable/finite-prefix predicate → Raw round-trip).
  - **`research-notes/G152_residue_self_covering.md`** — synthesis note (the
    full intellectual thread; file map; this open problem).
  - **`research-notes/data/probes/raw_branching_shape.py`** (+png) — Raw
    branching simulation, self-checks SET-EQUAL to Lean `RawDepth3.depthLe3List`.
    Findings: residue ratio → 1 (structure recedes from the complete-graph
    "void" in proportion); 1D Lens collapses |S_n| onto 2^n+1 dyadic positions;
    growth exponent = 2 = NT.
  - **`theory/essays/tower_atlas.md`** — boundary section (which repo "towers"
    are P-orbit readings vs distinct constructions); dropped deprecated N_U.
  - **`algebra_tower.md`** frontier fixed; **`G150`** trimmed.

### Where the discussion landed (for the next session)

The driving question "is the residue a GAP between 2 and 3 or the UNDIVIDED
thing both are?" dissolved, not answered:

  - "gap" is the *separation-view* reading; "undifferentiated" is the
    *non-separation-view* reading; **the residue is neither — it is what both
    views read.**  Raw has no "separation/non-separation" predicate either;
    both are Lens readings (per `seed/AXIOM/05_no_exterior.md` §5.4, §6.5).
  - Formally, only `object1_not_surjective` touches the residue *itself*: it is
    the surplus outside *every* pointing-view's image.  `object1_injective` /
    `distinct_equiv` / `residue_witnessed` are each one **view's survey**, not
    the residue.
  - The "1" (`Mobius213OneAsGlue`): `det(P) = NS − NT` proves gap = glue = the
    same 1 — the **rotation axis** 2 and 3 interconvert around, not an interval.
    0 = collapse (swap-fixed diagonal); 1 = the undivided unit.  Originator's
    own words: "1이 회전축, 2-1-3 불가분."
  - Method (Mingu): to investigate the "몰루" (the indeterminate — what cannot
    be seen as any single state) you must survey **all** sides — separation and
    non-separation views both.  Every view is a variation of the most primitive
    act = **pointing (지칭)**; "Raw = the residue of pointing" is itself the
    *most primitive view*, not a final description.

## Follow-up bricks this session (open problem RESOLVED + marathon)

  - **"One closure or two?" — answered: TWO, mutually supporting.**
    `Theory/Raw/Lambek.lean` (8 PURE): `decompose` (Lambek forward, the pointing
    act is a fixed point of its constructor shape — holds for μF and νF alike)
    + `depth_drops`/`atoms_are_floor` (well-founded, selects the LEAST fixed
    point); `two_closures` bundles them — neither implies the other, Raw = μF is
    their conjunction.  Also `self_similar_peel`/`self_similar_floor` (the floor
    = fixed shape under refinement, not a stipulated stop).
  - **Method note** `research-notes/G153_method_labelling_toward_residue.md` —
    why one slips (distributional gravity toward a fixed standpoint; 213 has
    none) + the positive method (labelling is the limit and the only method;
    many labels' common shadow narrows the residue's outline; never promote a
    shadow to identity).  CLAUDE.md gained the "View promoted to identity"
    failure mode.
  - **Marathon (3 continuations of G153, all closed):**
    · #2 `Lib/Math/Real213/ObjectIsReadingScaleInvariant.lean` (4 PURE) —
      object = reading is scale-invariant (atom `Object1 : Raw→(Raw→Bool)`;
      limit `RealAsLensOutput = Nat→(Nat→Bool)`); one shape `Index→Bool`.
    · #1 `Lib/Math/SelfSimilarityBridge.lean` (3 PURE) —
      `self_similarity_two_readings`: the form reading (Raw `self_similar_floor`)
      and the count reading (`numV(m+n) = numV m · numV n`, the `5^L`
      level-replication) are one self-similarity, two Lenses.
    · #3 `Lib/Math/DualCollapseCapstone.lean` (1 PURE) —
      `every_dual_is_one_shape`: four duals (decompose/build, object/morphism,
      object/reading, difference/identity) each one shape under the pointing
      view; the shared column made explicit (convergence evidence, not capture).

## φ self-similarity arc CLOSED + written up as a chapter

`fib_convergent_below_phi` ∀n (`Lib/Math/Real213/FibCassiniNat.lean`, PURE)
completes the arc: every Fibonacci/Pell convergent is below φ, native-Nat ∀n.
Primary narrative now at **`theory/math/phi_self_similarity.md`** (registered in
`theory/math/INDEX.md`, linked from `THEORY_BOOK.md §IV` self-form section) —
the paper-grade write-up of the three-readings result.  Larger frame stays in
`tower_atlas.md` / `THEORY_BOOK`; follow-on directions are the OPEN items below.

## φ-side CLOSED — self-similarity now has all three readings

`Lib/Math/SelfSimilarityBridge.lean` (5 PURE) — `self_similarity_three_readings`:
"same shape under descent" is one self-similarity from the (NS,NT)=(3,2)
signature read three ways —
  · **form** (Raw `self_similar_floor`): constructor shape invariant, atomic floor;
  · **count** (`self_similar_count`): level count replicates by `d = 5 = disc P`
    (`numV (m+n) = numV m · numV n`);
  · **limit-ratio** (`self_similar_ratio_is_phi`): the P-orbit consecutive-term
    ratio settles on the irrational fixed point φ (`tower_growth_phi_squared_bracket`
    ∈ (2,3)=φ², `phi_bracket_via_pell` brackets φ as a Cut).
The rational factor `5` and irrational `φ` are invariants of the *same* matrix P,
so the three are one self-similarity, not three coincidences.  This also realises
"걸림 = the self-fixed-point, which is why φ appears": the descent that keeps the
same shape converges to φ because φ is P's fixed point.

## φ limit-ratio PINNED (this session)

`Real213/PhiConvergence.lean` (4 PURE) + `SelfSimilarityBridge.self_similar_ratio_pins_phi`
(6 PURE in bridge): the Pell convergents form a **nested** sequence of rational
brackets (`convergents_nest`: cross-products ±1) whose widths **strictly shrink**
(`bracket_width_shrinks` via `pellDen_strictly_increasing`), pinning a *unique*
value in `[3/2, 5/3]` — φ (`phi_is_unique_nested_limit`).  Upgrades the
limit-ratio reading from "bracketed" to "pinned": a strictly-shrinking nested
rational sequence determines at most one real, and that real is φ.

## φ as a single ValidCut — DONE (this session)

`Real213/PhiAsCut.lean` (5 PURE): φ has a **closed-form decidable cut** — no
Cauchy-completion needed.  `phiCut m k := decide (k ≤ 2m ∧ 5k² ≤ (2m−k)²)` (from
`x² = x+1`: `m/k ≥ φ ⟺ (2m−k)² ≥ 5k²` with sign guard), and `phiCut_valid :
ValidCut phiCut` (both monotonicities, direct Nat arithmetic).  So the
residue's irrational limit-ratio signature is one 213-native Cut object, built
with no completion machinery.  `phiCut_brackets` cross-checks it against the
Pell convergents (8/5 < φ, 5/3 > φ, 13/8 > φ, 21/13 < φ).

The full self-similarity arc is now closed: form (`self_similar_floor`) / count
(`self_similar_count`, factor `5 = disc P`) / limit-ratio (φ, pinned by
`PhiConvergence` and realised as a Cut by `PhiAsCut`) — one self-similarity,
three readings, irrational signature a concrete object.

## φ-norm ∀n DONE; phiCut=false ∀n mechanism in place (this session)

`Real213/PhiNormInvariant.lean` (3 PURE): the φ-norm `num_n² − num_n·den_n −
den_n² = −1` for **all n** (`phi_norm_eq_neg_one`), generalising
`PhiCutConvergents.convergent_norm_form`'s layers-0..8 `decide`.  Route:
`coupling` (the `P = [[2,1],[1,1]]` matrix action `num_{n+1} = 2·num_n + den_n`,
`den_{n+1} = num_n + den_n`, by induction on the shared recurrence) →
`norm_eq_pell_unit` (single-layer φ-norm = consecutive cross-product
`pell_unit_at n`, the Int identity `qid`) → `pell_unit = −1`
(`mobius_213_pell_unit_invariant_forall`).  All manual `Int213` rewrites, no
`ring`/`omega`/Mathlib.

## φ as a Cauchy-complete limit object — DONE (this session)

The chosen target is **closed**.  φ is now built two ways that agree on the nose:
directly as one closed-form `ValidCut` (`PhiAsCut.phiCut`) and as the
Cauchy-complete limit of the rational Pell convergents
(`PhiCauchyLimit.phiConvergentSeq.limit`).

  - ★ `FibCassiniNat.cs_eq_phiCut` (12/12 PURE) — for every target `(m,k)` and
    every layer `i ≥ 2k`: `decide (fib(2i+2)·k ≤ fib(2i+1)·m) = phiCut m k`.
    **Stronger than Cauchy** — the cut sequence is eventually *constant* and
    equals the closed-form cut.  Honest pure-Nat modulus `N(m,k) = 2k`: squaring
    the cross-inequality collapses the whole √5 comparison to `fib(2i+1) > 2k`,
    reached by `fib_lb` (`i+1 ≤ fib(2i+1)`).  Case A (≥ φ) `true` ∀ layer
    (`cs_true_of_ineqs`); case B (< φ) `false` past modulus
    (`cs_false_of_below`/`cs_false_of_small`, strict mirror `gt_cross`/`qb_lt_pk`).
  - ★ `PhiCauchyLimit.phiCauchy_limit_eq_phiCut` (3/3 PURE) — assembles
    `CauchyCutSeq` (cs := native-Nat `convergentCS`, N := `2k`, cauchy from
    `cs_eq_phiCut`) and proves `phiConvergentSeq.limit m k = phiCut m k` pointwise
    (function `=` would pull `Quot.sound` via `funext`; pointwise is the 0-axiom
    form).
  - Written up: `theory/math/phi_self_similarity.md` §3.5 + Boundary update.
  - **Two old-note corrections (both probed, not assumed)**: (1)
    `of_decide_eq_true` on the φ-cut `And` is **PURE** — the feared "bool→Prop
    extraction" was a non-issue; the `cs_eq_phiCut` case-split uses it freely.
    (2) The lone `[propext]` in case A came **only** through
    `Nat.exists_eq_add_of_lt` inside `mul_lt_mul_r` (re-routed via `(b+1)·a ≤
    c·a`); `Nat.lt_or_ge`/`Nat.not_le` are PURE and were never the problem.
  - Built natively on `fib`; the canonical `Int`-seq `pellConvergentCut` then
    inherits it through the bridge below.

## Pell↔Fibonacci bridge — DONE (this session), Int→Nat wall cleared

The old "no PURE Int→Nat bridge" caveat is **removed**.
`PellFibCutBridge.pellNum_eq_fib` / `pellDen_eq_fib` (PURE, ∀n):
`pellNum n = fib(2n+2)`, `pellDen n = fib(2n+1)`.

  - **Key insight**: `((n : Nat) : Int).toNat = n` is `rfl` — the `toNat`
    read-out is harmless once `P_numerator.seq n` is pinned to a `natCast`.  So
    prove the `Int`-level `seq n = (fib · : Int)` by 2-step paired induction over
    the shared Pell recurrence `a(n+2) = 3a(n+1) − a(n)`, matched on the `fib`
    side by the additive `fib(2n+6) + fib(2n+2) = 3·fib(2n+4)` (`fib_even_3step`).
  - **All additive** — no `Int` subtraction (`Int.add_right_neg` pulls propext;
    routed via PURE `Int213.{add_comm, add_left_neg, neg_mul, add_assoc}`), no
    `omega`, no cast lemmas (`Int.toNat_natCast`/`exact_mod_cast` pull propext).
  - Capstone `pellConvergentCut_eq_phiCut`: the canonical Pell convergent cut
    stabilizes to `phiCut` ∀ target, every layer `i ≥ 2k`.  4/4 PURE.

## Completeness as a relocated operation + the completion tower — DONE (this session)

Foundational thread (originator: defining reals via completeness is a workaround;
213 makes them tangible without it).  Narrative chapter
`theory/math/completeness_relocated.md` (no Lean touched — promotion of PURE
results); four claims each an existing Lean fact (A `PhiAsCut.phiCut` / B import
graph / C `PhiAbCut.phiCompletion_limit_eq_phiCut` / D `EulerCut`+`PiCut`
hypothesis-modulus + `MonotonicBounded` §180–194 LEM refusal).  Tangibility =
queryability, NOT finiteness (`N_U` named as the discarded failure mode).

Then the "group the thresholds, then group the groupings, …" question — answered
**closed, not regress**:

  - `Analysis/CompletionTower.lean` (7 PURE) — completion is a fixed point.  Type
    closure (`limit : CauchyCutSeq → cut`, same type; `tower_stays_in_cut`),
    collapse (`tower_is_single_inner`, level-2 = one inner completion by `rfl`;
    `completion_idempotent`), value-stable (`tower_value_stable`).  = Lambek
    `self_similar_floor` at the cut scale.
  - `Analysis/ModulusMonoid.lean` (13 PURE) — "only the modulus moves" as a
    theorem.  Moduli form pointwise `(ℕ→ℕ→ℕ, madd, mzero)` = `(ℕ,+,0)`
    (`madd_assoc`/`comm`/`zero_{l,r}`); tower is its action
    (`tower_resolves_at_madd` — stacking levels adds moduli;
    `identity_level_is_mzero`).  ResolutionShift scalar grades embed as the
    constant sub-monoid via the monoid hom `gradeToModulus`
    (`gradeToModulus_add`, `shift_grade_embeds`) — grouping-of-groupings and
    resolution-shifting are one `(ℕ,+)`.
  - `Analysis/ResolutionQuantitative.lean` (6 PURE) — the grade's *quantitative*
    meaning.  `grade_scales_denominator` (grade n = `2ⁿ` finer: `dyadicCut M E ↦
    constCut M (2^(E+n))`), `grade_add_multiplies` (`2^(a+b)=2^a·2^b`, additive
    grade ↔ multiplicative resolution; `two_pow_add` PURE), `resolution_is_measurable`
    (grade unique → faithful), `resolution_realised`.  Closes the thesis loop:
    the modulus is a measurable, composable amount of resolution, not abstract
    bookkeeping.  **Scoped to the dyadic slice** — see ModulusForm.
  - `Analysis/ModulusForm.lean` (6 PURE) — answers "is 2^n enough to decide every
    real?": NO, and corrects the ResolutionQuantitative reading.  The probe space
    is every rational m/k; the resolving modulus is a function of the probe (ℕ→ℕ→ℕ),
    constant 2^n grades a razor-thin slice.  Per-real forms: dyadic = constant
    grade, φ = `2*k` (linear, `phi_modulus_exceeds_every_grade`), e = n!-paced.
    `grade_class_is_proper`: φ's modulus resolves φ yet lies outside the
    constant-grade image — the grade monoid is a PROPER sub-structure.  The modulus
    form is a per-real invariant (originator's intuition, confirmed).

## e, π, φ as Real213 cuts via `AbCutSeq` — DONE (this session)

Transcendentals (and φ) lifted from the Raw/`orderProj` level (`Cauchy/Euler`,
`Cauchy/Wallis`, Fibonacci convergents) to the `Real213` `ValidCut` level,
unified under one structure:

  - `Real213/AbCutSeq.lean` (8 PURE) — ★ **every monotone-bounded ab-sequence is a
    `Real213` cut**.  `structure AbCutSeq := (xs : Nat→Raw) (mono : IsAbMonotonic)
    (pos : IsAbPositiveB)`; `cut`/`cut_valid`/`cut_ratio`/`cut_false_fwd`
    (nesting)/`cut_eventually_const`/`toCauchy`/`toCauchy_limit_valid`/
    `limit_brackets` (generic localization transport) all live once here.
  - `Real213/ExpLog/EulerCut.lean` (10 PURE) — e as `eAb : AbCutSeq` + localization
    in (8/3, 3) (`eulerCut_in_8_3_to_3`).  Thin instance.
  - `Real213/ExpLog/PiCut.lean` (16 PURE) — π/2 as `piHalfAb`, π/2 ∈ (7/5, 2);
    `piCut n m k := halfPiCut n m (2k)`, π ∈ (14/5, 4).  Sharp lower bound from
    `W₂ = 64/45 > 7/5` by `decide` at n=2 + nesting (avoids `omega`-dirty
    `wallis_sharper_lower`).
  - `Real213/PhiAbCut.lean` (11 PURE) — ★ **φ as `phiAb : AbCutSeq`**; convergent
    monotonicity IS the Cassini norm (`cassini_mono_step`, +1 gap).

  - **Structural finding — the algebraic/transcendental split, now a THEOREM**:
    all three share the `AbCutSeq` carrier; the *only* difference is the
    completion modulus.  φ's is **closed-form** `N=2k` with no hypothesis
    (`phi_cut_eventually_const` via `cs_eq_phiCut`), so `phiCompletion :
    CauchyCutSeq` is a closed term and `phiCompletion_limit_eq_phiCut` recovers
    `PhiAsCut.phiCut`.  e/π have **no** closed-form total modulus (it would be the
    global order-Cauchy closure `Cauchy/MonotonicBounded` §180–194 refuses as
    smuggled LEM), so their `toCauchy` takes the modulus as a **hypothesis**.
    Algebraicity *is* exactly the closed-form modulus.

## General Cauchy completeness — DONE (this session)

`Analysis/CauchyCompleteValid.lean` — the cut space is *closed* under Cauchy
limits, beyond per-instance constructions (3 theorems, all PURE):

  - `CauchyCutSeq.limit_valid` : `(∀ i, ValidCut (cs i)) → ValidCut limit`
  - `CauchyCutSeq.limit_ratio` : `(∀ i, RatioCut (cs i)) → RatioCut limit`
  - `CauchyCutSeq.limit_unique`: `(∀ i m k, c1.cs … = c2.cs …) → c1.limit m k =
    c2.limit m k` — limit depends only on `cs`, not the modulus (pointwise).

  - **Uniform proof**: two points `limit · ·` sample at different moduli `N`;
    pull both to one common index `N₁ + N₂` past both via `limit_eq_at`, then
    apply the single term's own monotonicity.
  - **Purity note**: common index is `N₁ + N₂` (not `Nat.max`, whose lemmas pull
    `propext`), and `limit_unique` is pointwise (not function-eq, which pulls
    `funext`/`Quot.sound`).  The first commit (`aac014f`) used `max`/`funext` and
    was axiom-dirty — caught by `scan_axioms` and fixed in `e8a1d02`.  Sibling
    file keeps `CauchyComplete` free of the `Real213.Core.ValidCut` dependency;
    aggregator `Analysis.lean` imports it.

## Pell/Cassini norm step — CONSOLIDATED (this session)

`FibCassiniNat.normstep` and `Mobius213PellInvariant.pell_step` were the SAME
statement (the Möbius P-step `(a,b)↦(2a+b,a+b)` preserves `a²+1 = a·b+b²`),
proved twice.  Now **one** public engine `Mobius213PellInvariant.pellNormStep`;
`FibCassiniNat`'s ~70-line private duplicate cluster (`tt…eR, hR, normstep`)
deleted, `fib_cassini_norm` cites the shared lemma.  Net −62 lines, 0 dup.

## OPEN (next targets — pick up here)

  - **GRA-tower ↔ CD-tower duality** (conceptual only, `tower_atlas.md` open
    frontier): level `n` of property-loss ↔ level `5−n` of Reading-iso gain.
  - **Flexibility over a non-associative base** (`CDDoubleFlexible.lean`
    cross-pair crux) — the long-standing Cayley-Dickson open item.

## Notes / hygiene

  - N_U = d^(d²) is **deprecated** (audit branch `claude/full-file-audit-ChymR`
    `bbd07b5`); `seed/RESOLUTION_LIMIT_SPEC.md` does not exist (stale ref).
    Don't cite N_U as a constant; don't use "ℝ = final boss" framing (AI-introduced).
  - `decide` on `Subtype`/`Raw` equality pulls `propext` via `DecidableEq Raw`;
    use `Tree.noConfusion` (for `a≠b`) and `of_decide_eq_true` (NOT
    `decide_eq_true_eq`) to stay strict ∅-axiom.  Bit me twice this session.
  - Repo-first: `PredicateSelfEncoding` already existed; I nearly rebuilt it.
    Grep + INDEX before coding a "missing" cell.
