# G138 — Post-merge corpus synthesis (theory/ at 103 chapters)

**Status**: Synthesis note (Phase 7.6 of `ready-to-merge` skill).
Written after merging `origin/main` into the audit branch — the
corpus stabilised at 103 chapters across math/physics/lens/meta/essays,
with G126 / G128 / G129 / G130 promoted in parallel on the two
branches, and the L_11 Aurifeuillean attempt closed as out-of-reach.

## Anchor

103 chapters across five areas; eight closed sub-trees promoted in
the last marathon round; cardinality-cut-off + cup-ladder framework
documented as standalone meta methodology; α_em precision-theorem
stack at 0.007 ppb; modulus-structure 3-way bridge promoted.  The
corpus is dense enough that lateral synthesis can now identify
cross-chapter structural recurrences.

This note replaces (does not supersede) G137 — G137 captured
post-G134 cut-off-principle patterns; this one catches what surfaces
when reading the WHOLE corpus, including the post-merge additions
(`theory/math/analysis/modulus_structure.md`, `theory/essays/cut_off_marathon.md`).

## Six insights

### Pattern A — Modulus-functor unification across analytic disciplines

The `Nat → Nat` modulus shape (target precision ↦ step count) is
the 213-native replacement for ε-N convergence across at least four
independent contexts:

  · `IsContinuousModulus` (Topology/Continuity) — monotone modulus
    for cochain-function continuity.
  · `IsRicciModulus` (Geometrization/Ricci) — anti-monotone
    Ricci-flow step count.
  · `dyadic_bracket_cauchy_modulus` (Analysis) — linear `L · k`
    bracket-Cauchy modulus.
  · `zeta_modulus` (`AlphaEM/precision_derivation` Step 6) — α_em
    Gram-correction modulus.

`theory/math/analysis/modulus_structure.md` Option-A close documents the
3-way typeclass bridge between the first three.  The α_em
`zeta_modulus` is a fourth instance that has NOT been added to the
3-way framework yet — it lives in a different sub-tree but carries
the same `Nat → Nat` shape with monotonicity property.

**Action**: extend `IsModulusStructure` projections to include
the AlphaEM modulus; this would lift the framework from
3-way → 4-way and surface the modulus-functor as the universal
form of "constructive approach to limit" across the corpus.
Likely 5-10 PURE.  Open Frontier item for the next ModulusStructure
session.

### Pattern B — Sym(3) spine across four domains

The Sym(3) representation-theoretic decomposition `8 = 2·trivial
⊕ 3·standard` reappears in four independent chapters as the
load-bearing irrep structure:

  · `math/cohomology/k32_higher_cohomology.md` §Sym(3)-invariant —
    H¹(K_{3,2}^{(c=2)}) = 2·trivial ⊕ 3·standard, dim 8.
  · `math/geometrization_conjecture.md` step 24 — 8 Thurston
    geometries decompose under Sym(3) as 3 isotropic + 5 anisotropic.
  · `physics/alpha_em/precision_derivation.md` §5 — 1/α_3 = NS² − 1
    = 8 = dim adj SU(3), the gluon octet.
  · `math/exotic_4mfd_cork.md` — cork-twist on the 8-dim H¹ basis
    via M_S01 Sym(3) generator.

The four ARE the same Sym(3) action on the same K_{3,2}^{(c=2)}
H¹ basis, viewed through different Lens choices.
`X1_sym3_cross_frame_capstone` (in GeometrizationConjecture/CrossFrame)
records the 4-way convergence as a single theorem, but the corpus
does not yet have a single chapter that EXPOSITS the Sym(3) spine
itself as a central object.

**Action**: write a chapter `theory/math/cohomology/sym3_spine.md` (Pattern 2
narrative-from-scratch) collecting the four readings + the
cross-frame capstone + a "why Sym(3) at d = 5" structural
explanation.  Bridges cohomology, geometrization, physics, exotic
4-mfd.  Mid-effort (~150 lines, no new Lean).

### Pattern C — Cut-off principle as general meta-methodology

The cardinality cut-off principle (G133 / G134) was born from
Aurifeuillean cyclotomic analysis but the three-step pattern
(locate / diagnose-literal-failure / prove-refined-form) reappears
structurally elsewhere:

  · `math/dyadic_fsm.md` Pell-Fibonacci universal closure —
    split/inert/ramified case split on `legendre213 5 p` is exactly
    a locate-the-cut + diagnose-failure + prove-refined-per-case
    pattern.
  · `physics/foundations/atomic_constants.md` C2b monotonicity —
    bounds at (n=2, n=3, n≥3) identify where the literal constraint
    fails, then prove the refined-with-case-split version.
  · `math/cohomology/cup_ladder_graduation.md` max α-power = top
    skeleton dim + 1 — `(k+1)`-skeleton extension trivialises the
    previous H^k contribution; this is "cut-off the cohomology
    where it vanishes" with the same shape.

**Action**: extend `theory/meta/cardinality_cutoff_principle.md`
with an "Other instantiations" section pointing at these three.
Or, if the pattern feels generic enough, write a separate
`theory/meta/cut_off_meta_methodology.md` that names the
three-step recipe.

### Pattern D — Clause-4 recursive Lens application as postulate-derivation

The 213 axiom Clause 4 (self-pairing prohibition `x/x` forbidden)
applied recursively at non-atomic granularity DERIVES predicates
that look postulated.  One instance is closed; two more candidates
sit ready:

  · CLOSED: `IsAlive ↔ IsClause4Alive` (AliveDerivation.lean) —
    the alive predicate (both a, b odd) IS the count-Lens reading
    of Clause-4 applied to NT-pairs and NS-triples.  Pattern #9
    in `theory/meta/methodology_patterns.md`.
  · OPEN candidate 1: Nodup constraints in cohomology — every
    `List.Nodup` requirement at the face / cochain level is
    Clause-4 applied at list granularity.
  · OPEN candidate 2: colex sorted-uniqueness — sortedness is
    Clause-1 (distinguishing) applied recursively, producing
    canonical ordering.

**Action**: take Nodup as a target — write `lean/E213/.../NodupAsClause4.lean`
proving Nodup is the recursive Clause-4 application at list level.
Small (~20-30 PURE).  Promotes Pattern #9 from one example to
two-three examples, demonstrating it's a methodology, not a
one-off.

### Pattern E — `Int.NonNeg` constructor inversion as propext bypass

Pattern #8 in `methodology_patterns.md` documents a mechanical
refactor: any DIRTY theorem invoking `omega` or `Int`-ordering
lemmas that drag in `propext` can be replaced by direct
`Int.NonNeg` constructor matching.  The pattern is fully documented;
three instances are live (ZOmegaUnits, KSubsetStructural,
FinBridgeGeneral); ~50 more DIRTY sites are candidates.

**Action**: run a scanner pass (`tools/scan_axioms.py` + grep for
`omega` in proof bodies) to enumerate the ~50 candidates, then
batch-refactor in a dedicated session.  Net effect: ~50 DIRTY
theorems → PURE.  Yields immediately at the
DRLT Validation Standard tier.

### Pattern F — Framework-internal subsumption doctrine

Pattern #17 + #20 in `methodology_patterns.md` identify four
canonical concepts where 213 maintains MULTIPLE coexisting
realisations rather than picking one canonical form:

  · Real213: struct vs Lens-output vs DyadicBracket carriers
  · Derivative: limit vs localDivergence vs IsDifferentiable
  · Cup product: standard `cup` (lex-projection) vs `cupAW`
    (Alexander–Whitney) — both PURE, neither canonical
  · Modulus: continuity vs Ricci vs Cauchy-bracket (`theory/math/analysis/modulus_structure.md`)

This is not indecision; it's systematic doctrine.  The corpus
refuses to pick a canonical form when multiple framework-internal
realisations exist.

**Action**: write `theory/meta/multiplicity_doctrine.md` collecting
the four instances + their pairwise bridges (where bridges exist)
+ a statement of the doctrine.  Cross-references Pattern #17 and
#20 explicitly.  Most synthetically dense item; ~120-180 lines.

## Cross-references

- Pattern A: `theory/math/analysis/modulus_structure.md`,
  `theory/physics/alpha_em/precision_derivation.md` Step 6
- Pattern B: `theory/math/cohomology/k32_higher_cohomology.md`,
  `theory/math/geometry/geometrization_conjecture.md`,
  `theory/physics/alpha_em/precision_derivation.md`,
  `theory/math/geometry/exotic_4mfd_cork.md`
- Pattern C: `theory/meta/cardinality_cutoff_principle.md`,
  `theory/math/numbertheory/dyadic_fsm.md`,
  `theory/physics/foundations/atomic_constants.md`,
  `theory/math/cohomology/cup_ladder_graduation.md`
- Pattern D: `theory/meta/methodology_patterns.md` Pattern #9,
  `AliveDerivation.lean`
- Pattern E: `theory/meta/methodology_patterns.md` Pattern #8
- Pattern F: `theory/meta/methodology_patterns.md` Patterns #17 / #20,
  `theory/math/analysis/modulus_structure.md`,
  `theory/math/cohomology/cup.md` (lex-vs-AW coexistence)

## Priority ranking

If only one of these is taken up next:

1. **Pattern B (Sym(3) spine chapter)** — highest synthesis density,
   no new Lean needed, closes a chapter-shaped hole in the corpus.
2. **Pattern E (Int.NonNeg refactoring sweep)** — highest mechanical
   yield (50 DIRTY → PURE), directly advances DRLT Validation Standard.
3. **Pattern F (multiplicity-doctrine chapter)** — doctrinal
   consolidation; helps onboarding.
4. **Pattern A (4-way ModulusStructure extension)** — small Lean
   addition + chapter update.
5. **Pattern D (Nodup as Clause-4)** — one Lean file, promotes
   Pattern #9 to a methodology.
6. **Pattern C (cut-off meta-methodology chapter)** — chapter
   restructure within `theory/meta/`.
